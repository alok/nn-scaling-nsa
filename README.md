# Lecture Notes on Neural Network Scaling Limits — Nonstandard & Clifford Analysis Editions

A two-stage mathematical rewrite and Lean 4 / Verso formalization of Mufan Li's 98-page [*Lecture Notes on Neural Network Scaling Limits*](https://mufan-li.github.io/files/Lecture%20Notes/nn_scaling.pdf) (STAT 946, University of Waterloo), preserving Mufan Li's prose, narrative structure, theorem numbering, figures, tables, and exercises while upgrading the mathematical engine in two cleanly separated stages:

1. **Stage 1 — Pure Nonstandard Analysis (`nsa` bookmark):** [`pdf/nn_scaling_nsa.pdf`](pdf/nn_scaling_nsa.pdf) (108 pages) — every asymptotic scaling limit ($n \to \infty$, $d/n \to \bar{\tau}$, $O_{\mathbb{P}}(n^{-1/2})$) is replaced by exact algebra at hyperfinite network dimensions $N, D, M \in {}^*\mathbb{N} \setminus \mathbb{N}$ over Robinson's enlargement $({}^*\mathbb{R}, {}^*\mathbb{N})$ and Loeb probability spaces $(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))$.
2. **Stage 2 — Nonstandard Clifford Analysis (`main` bookmark):** [`pdf/nn_scaling_clifford.pdf`](pdf/nn_scaling_clifford.pdf) (111 pages) — built strictly on top of Stage 1, upgrading feature/gradient Gram matrices, Cho–Saul arc-cosine kernels, Gaussian conditioning, double-descent Schur complements, Otto–Wasserstein mean-field PDEs, Transformer key–query products, and Dyson Brownian motion into Euclidean and hyperreal Clifford algebras $\mathcal{C}\ell_n(\mathbb{R})$, $\mathcal{C}\ell_n(\mathbb{L})$, and ${}^*\mathcal{C}\ell_N$.

* **Exhaustive Developer & Mathematical Guide:** [`DEVELOPER_GUIDE.md`](DEVELOPER_GUIDE.md)
* **Complete Monograph-to-Lean Coverage Matrix:** [`COVERAGE.md`](COVERAGE.md)
* **Architectural Specification:** [`SPEC.md`](SPEC.md)

---

## Core Mathematical Synthesis

### Stage 1: Robinson's Enlargement & Loeb Shadows (`nsa`)
* **Asymptotic hierarchies become commutative algebra:** Boundedness $O(1)$, vanishing errors $o(1)$, and exact scale matching $\Theta(1)$ / $\asymp$ become membership in the valuation subring of **limited hyperreals** $\mathbb{L} \subset {}^*\mathbb{R}$, its maximal ideal of **infinitesimals** $\mathbb{I}$ ($x \approx y$), and the multiplicative group of **appreciable hyperreals** $\mathbb{A} = \mathbb{L} \setminus \mathbb{I}$ ($x \asymp y$).
* **Distributional and process limits become standard parts:** Applying the surjective ring homomorphism $\operatorname{st} : \mathbb{L} \to \mathbb{R}$ ($\ker \operatorname{st} = \mathbb{I}$) on Loeb spaces $(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))$ turns NNGP/NTK concentration, Wishart double descent, McKean–Vlasov propagation of chaos, and Keisler–Lindstrøm covariance SDEs into exact shadow evaluations.

### Stage 2: Nonstandard Clifford Analysis (`nsa..main`)
* **Multivector standard-part homomorphism (`NNScaling/Clifford.lean`):** Lifting $\operatorname{st} : \mathbb{L} \to \mathbb{R}$ via `CliffordAlgebra.lift` produces a canonical ring homomorphism $\operatorname{st}_{\mathcal{C}\ell} : \mathcal{C}\ell_n(\mathbb{L}) \to \mathcal{C}\ell_n(\mathbb{R})$ (`stCliffordHom`) that commutes with the full geometric product and annihilates infinitesimal scalars and vectors.
* **Unit bivectors $\hat{B}^2 = -1$ unify three chapters:** Orthogonal unit vectors generate bivectors $\hat{B} = e_1 e_2$ satisfying $\hat{B}^{\sim} = -\hat{B}$ and $\hat{B}^2 = -1$ (`unit_bivector_sq_neg_one`), simultaneously driving:
  1. **Chapter 2:** Cho–Saul ReLU kernel via the input-plane rotor $u_1 u_2 = \rho + \sqrt{1-\rho^2}\,\hat{B}$ (`choSaul_rotor_unit_norm`);
  2. **Chapters 1 & 6:** Cauchy–Dirac Stieltjes resolvents in $\mathcal{C}\ell_2^+ \cong \mathbb{C}$ (`cauchy_dirac_resolvent_norm`);
  3. **Chapter 6:** Eigenvalue repulsion $+\sum_{j\neq i}\frac{\lambda_i\lambda_j}{\lambda_i - \lambda_j}\,d\tau$ in Geometric Dyson Brownian Motion via two-sided spinor eigenframe transport $u_k(\tau) = R_\tau e_k R_\tau^{\sim}$ in $\operatorname{Spin}(m) \subset \mathcal{C}\ell_m^+$ (`planarRotor_sandwich_e1`, `spin_eigenframe_repulsion_balance`).
* **Hestenes blades & monogenic Dirac calculus:**
  * **Chapters 2, 3, & Appendix A:** Moore–Penrose subspace projectors become basis-free blade contractions $(w \lrcorner \bm{\Phi})\bm{\Phi}^{-1}$ and exterior rejections $(w \wedge \bm{\Phi})\bm{\Phi}^{-1}$, while the inverse-Wishart double-descent spike becomes the exterior wedge-volume ratio $\lVert g_1 \wedge \bm{G}_2\rVert^2 / \lVert \bm{G}_2\rVert^2$ (`lagrange_bivector_schur_complement`).
  * **Chapters 2 & 4:** Parameter Dirac operators $\partial_\theta$ split tangent products into symmetric scalar NTK $K_t^{(N)}$ plus antisymmetric bivector curl $\Omega_t^{(N)}$ (`bivector_curl_quadForm_zero`), and express the Otto–Wasserstein mean-field PDE as $\partial_t \rho_t + \langle \partial_\theta(v_t\rho_t)\rangle_0 = 0$ with monogenic curl-free velocity $\langle \partial_\theta v_t\rangle_2 = 0$ (`monogenic_gradient_bivector_curl_zero`).

---

## Repository Layout

```text
nn-scaling-nsa/
├── pdf/
│   ├── nn_scaling_nsa.pdf              # Stage 1 pure NSA monograph (108 pages, preserved from `nsa`)
│   └── nn_scaling_clifford.pdf         # Stage 2 Nonstandard Clifford Analysis monograph (111 pages)
├── tex/
│   ├── main.tex                        # Top-level LaTeX report entry point
│   ├── preamble.tex                    # Theorem counters + hyperreal/Loeb + Clifford/Dirac macros
│   ├── ch01_intro.tex                  # Ch 1: Scaling laws, CLT, Cauchy–Dirac semicircle, Dirac PDE
│   ├── notation.tex                    # Standard + NSA + Clifford/Spin notation table
│   ├── ch02_kernels.tex                # Ch 2: Rotor NNGP, Dirac NTK curl split, blade conditioning
│   ├── ch03_double_descent.tex         # Ch 3: Wedge-volume Schur complement & subspace blades
│   ├── ch04_feature_learning.tex       # Ch 4: Dirac continuity PDE, curl-free Wasserstein flow, μP
│   ├── ch05_depth_sde.tex              # Ch 5: Clifford vector squares & covariance SDE shadows
│   ├── ch06_proportional_topics.tex    # Ch 6: Attention multivectors, Spin(m) Dyson BM, Cl₂⁺ Burgers
│   ├── appa_technical.tex              # App A: Dirac weak adjointness, Skorohod SDEs, blade projections
│   ├── acknowledgements.tex            # Attribution & two-stage editorial note
│   ├── refs.bib                        # Original + NSA + Clifford/Geometric Algebra bibliography
│   └── figures/                        # Reproducible vector PDF plots
├── NNScaling/
│   ├── Foundations.lean                # 0A: ℝ* scale algebra (𝕃, 𝕀, 𝔸, st) & Loeb interfaces
│   ├── Clifford.lean                   # 0B: LimitedSubring, stRingHom, rotors, blades, stCliffordHom
│   ├── Ch01_Introduction.lean          # Hyperfinite scaling microscope, semicircle, Cl₂⁺ resolvent
│   ├── Ch02_Kernels.lean               # Gram PSD, Cho–Saul rotor, NTK dissipation & curl cancellation
│   ├── Ch03_DoubleDescent.lean         # Hyperfinite Wishart st, Lagrange wedge Schur, Exercises 3.4
│   ├── Ch04_FeatureLearning.lean       # μP exponent uniqueness, hyperreal scale, monogenic curl = 0
│   ├── Ch05_DepthSDE.lean              # Isserlis tensor, GBM drifts, blowup ODE, ℝ* Clifford square
│   ├── Ch06_ProportionalTopics.lean    # Shaped attention, SPD congruence, Spin(m) repulsion, Burgers
│   └── AppendixA_Technical.lean        # Cometric duals, 4-block orthogonality, blade cancellation
├── NNScaling.lean                      # Verso literate landing page linking both PDFs & all modules
├── scripts/
│   ├── gen_figures.py                  # Reproducible vector figures (uv + matplotlib/scipy)
│   └── build_pdfs.sh                   # Helper script compiling tex/main.tex into pdf/
├── DEVELOPER_GUIDE.md                  # Exhaustive from-scratch engineering & mathematical guide
├── COVERAGE.md                         # Complete Stage 1 + Stage 2 monograph-to-Lean coverage matrix
└── SPEC.md                             # Two-stage architectural specification
```

---

## Jujutsu (`jj`) / Git Two-Stage Bookmark History

The repository history is organized linearly into two clean, narrative-quality stages:

* **`::nsa`** (9 atomic commits ending at bookmark `nsa`): Complete **Stage 1 (Pure Nonstandard Analysis)** build — Lean 4 / Verso setup, vector figures, Chapters 1–6 & Appendix A in pure NSA, `pdf/nn_scaling_nsa.pdf`, `NNScaling/Foundations.lean` + chapter formalizations, and GitHub Pages CI.
* **`nsa..main`** (7 atomic commits from `nsa` to bookmark `main`): Complete **Stage 2 (Nonstandard Clifford Analysis)** upgrade layered cleanly on top of `nsa` — Clifford specification, LaTeX geometric/Dirac upgrades, `pdf/nn_scaling_clifford.pdf`, `NNScaling/Clifford.lean` + Verso chapter upgrades, and `DEVELOPER_GUIDE.md`.

To inspect either stage directly:
```bash
jj log -r 'root()..main'
git diff nsa..main          # Inspect exact Stage 1 -> Stage 2 Nonstandard Clifford diff
```

---

## Building Locally

### 1. Lean 4 + Verso Literate Site (`v4.35.0`)

```bash
lake build
lake query :literateHtml
```

Every Lean module compiles with `autoImplicit = false`, **zero** custom axioms, and **zero** `sorry` placeholders.

### 2. LaTeX Monographs (`pdf/*.pdf`)

```bash
uv run --with matplotlib --with numpy --with scipy python3 scripts/gen_figures.py
./scripts/build_pdfs.sh clifford
```

---

## Attribution

Based on Mufan Li's *Lecture Notes on Neural Network Scaling Limits* (STAT 946, University of Waterloo, 2026). Nonstandard Analysis & Nonstandard Clifford Analysis editions and Lean 4 / Verso formalization by Alok Singh.
