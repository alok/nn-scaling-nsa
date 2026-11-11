# Specification: Lecture Notes on Neural Network Scaling Limits via Nonstandard Analysis

## 1. Purpose and Scope

This repository rewrites the mathematics of Mufan Li's *Lecture Notes on Neural Network Scaling Limits* (STAT 946, University of Waterloo, September 5, 2026 draft) into **Nonstandard Analysis (NSA)**, while preserving Mufan Li's exposition, narrative voice, chapter and section organization, examples, tables, figures, and exercises as closely as possible.

Two synchronized artifacts are maintained from the same mathematical development:

1. **Full LaTeX Book (`tex/` -> `pdf/nn_scaling_nsa.pdf`)**: A complete, publication-grade LaTeX monograph matching all 6 chapters, the Notation reference, all exercises, figures, tables, Appendix A, Acknowledgements, and Bibliography of Mufan Li's lecture notes, with limit-based asymptotic arguments replaced by hyperfinite and Loeb-measure Nonstandard Analysis.
2. **Verso / Lean 4 Literate Site (`NNScaling/` -> `:literateHtml`)**: A chapter-by-chapter Lean 4 (`v4.35.0`) + Mathlib + Verso literate formalization and interactive web book deployed via GitHub Pages (bundling the compiled PDF monograph).

## 2. Nonstandard Framework

We work in a countably saturated ($\aleph_1$-saturated) nonstandard enlargement $({}^*\mathbb{R}, {}^*\mathbb{N})$ of the real universe:

* **Hyperreal Magnitude Rings**:
  * $\mathbb{L} = \{x \in {}^*\mathbb{R} : \exists C \in \mathbb{R}_{>0},\; |x| \le C\}$ denotes the ring of *limited* hyperreals (replacing asymptotic $\mathcal{O}(1)$).
  * $\mathbb{I} = \{\varepsilon \in {}^*\mathbb{R} : \forall c \in \mathbb{R}_{>0},\; |\varepsilon| < c\}$ denotes the maximal ideal of *infinitesimals* ($\varepsilon \approx 0$, replacing $o(1)$).
  * $\mathbb{A} = \mathbb{L} \setminus \mathbb{I}$ denotes the multiplicative group of *appreciable* hyperreals (replacing $\Theta(1)$), with asymptotic equivalence $x \asymp y \iff x/y \in \mathbb{A}$.
  * $\operatorname{st} : \mathbb{L} \to \mathbb{R}$ is the *standard part* (shadow) homomorphism, characterized by $x \approx \operatorname{st}(x)$.
* **Loeb Probability Spaces**:
  * Every hyperfinite or internal probability space $(\Omega, \mathcal{A}, {}^*\mathbb{P})$ induces a complete, countably additive standard probability space $(\Omega, \mathcal{L}(\mathcal{A}), L(\mathbb{P}))$ via Loeb's construction, $L(\mathbb{P})(A) = \operatorname{st}({}^*\mathbb{P}(A))$ for $A \in \mathcal{A}$.
  * Weak convergence in distribution $Z^{(n)} \xrightarrow{d} Z$ and convergence in probability $X^{(n)} \xrightarrow{\mathbb{P}} c$ are replaced by *Loeb almost-sure shadows* $\operatorname{st}(Z^{(N)}) \sim Z$ and *infinitesimal concentration* $X^{(N)} \approx c$ in $L(\mathbb{P})$-probability at an unlimited hyperinteger $N \in {}^*\mathbb{N} \setminus \mathbb{N}$.
* **Path-Space Lifting (Anderson & Keisler)**:
  * Rescaled discrete processes over hyperfinite grids $\mathbb{T}_N = \{0, \Delta\tau, 2\Delta\tau, \dots\}$ with $\Delta\tau = 1/N \approx 0$ are analyzed via *S-continuity* and Keisler–Lindstrøm hyperfinite stochastic difference equations $\Delta X_\ell = b(X_\ell)\Delta\tau + \sigma(X_\ell)\Delta B_\ell + \tilde{o}_\ell(\Delta\tau)$, whose pointwise standard parts solve the corresponding standard Itô SDEs without Skorohod $J_1$ jump-time reparameterizations.

## 3. Chapter-by-Chapter Architecture

| Chapter | LaTeX File | Lean / Verso Module | Core Nonstandard Mechanism |
|---|---|---|---|
| 1. Introduction | `tex/ch01_intro.tex` | `NNScaling.Ch01_Introduction` | Scaling laws as leading infinitesimal microscope terms $N^\alpha({}^*L(x_N) - L_\infty) \approx c$; Anderson's hyperfinite Brownian motion; hyperfinite Wigner ESD shadow; Loeb McKean–Vlasov particles. |
| Notation | `tex/notation.tex` | `NNScaling.Foundations` | $\mathbb{L}, \mathbb{I}, \mathbb{A}$, $\approx$, $\operatorname{st}$, unlimited $N, D, M \in {}^*\mathbb{N}\setminus\mathbb{N}$, Loeb measure $L(\mathbb{P})$. |
| 2. Kernel Limits: NNGP & NTK | `tex/ch02_kernels.tex` | `NNScaling.Ch02_Kernels` | Unlimited width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$ at standard $d, m, n_0$; Loeb SLLN $\Phi_\ell^{(N)} \approx \Phi_\ell$; monadic parameter displacement $\frac{1}{N}\|\theta(s)-\theta(0)\|^2 \approx 0$ freezing $K_t^{(N)} \approx K$; internal Gaussian conditioning by Transfer. |
| 3. Double Descent | `tex/ch03_double_descent.tex` | `NNScaling.Ch03_DoubleDescent` | Proportional unlimited $(M, N_0, N)$ with $\gamma = \operatorname{st}(N_0/M)$ and $\delta = \operatorname{st}(N/M)$; internal QR/Moore–Penrose/Schur identities by Transfer + inverse-Wishart trace shadows. |
| 4. Feature Learning & Mean-Field | `tex/ch04_feature_learning.tex` | `NNScaling.Ch04_FeatureLearning` | Valuation-group algebra in ${}^*\mathbb{R}^\times/\mathbb{A}$ selecting $\gamma_N \asymp \sqrt{N}, \eta_N \asymp N$; Loeb pushforward $\rho_t = L(\rho_t^{(N)})\circ\operatorname{st}^{-1}$ solving weak continuity PDE; representative Loeb neuron for DMFT. |
| 5. Depth Scaling & Covariance SDE | `tex/ch05_depth_sde.tex` | `NNScaling.Ch05_DepthSDE` | Hyperfinite depth $D \in {}^*\mathbb{N}\setminus\mathbb{N}$; galaxy separation of $(N,D)$ routes ($D/N \approx 0$, $N/D \approx 0$, $\operatorname{st}(D/N)=\bar{\tau}$); Keisler–Itô Gram increment $\Delta\Phi_\ell = b(\Phi_\ell)\Delta\tau + \Sigma(\Phi_\ell)^{1/2}\Delta B_\ell + \tilde{o}_\ell(\Delta\tau)$; exit from appreciable SPD galaxy. |
| 6. Proportional Depth–Width Topics | `tex/ch06_proportional_topics.tex` | `NNScaling.Ch06_ProportionalTopics` | Unlimited attention temperature $s = s_0\sqrt{N n_k}$; infinitesimal Hadamard perturbation for Geometric Dyson BM; hyperfinite spectral Burgers PDE ($1 \ll M \ll N$); hyperfinite forward/reverse 6-equation overlap system for one training step. |
| Appendix A. Technical Complements | `tex/appa_technical.tex` | `NNScaling.AppendixA_Technical` | S-differentiability for transport PDE; monadic Hölder S-continuity on compacta; S-continuity & Keisler Markov-chain lifting; monadic SPD cometric; transferred one- and two-sided Gaussian conditioning. |

## 4. Verification Criteria

1. `latexmk -pdf` in `tex/` compiles cleanly with zero LaTeX errors, zero undefined citations, and zero undefined cross-references, producing `pdf/nn_scaling_nsa.pdf`.
2. `lake build` and `lake query :literateHtml` succeed cleanly on Lean `v4.35.0` with no custom axioms (`sorry` permitted only as explicit typed specifications for deep stochastic/analytic theorems beyond Mathlib).
3. All figures (`1.1`, `1.2`, `1.3`, `3.1`, `5.1`) are reproducibly generated from code/TikZ with vector output.
