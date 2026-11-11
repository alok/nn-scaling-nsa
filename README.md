# Lecture Notes on Neural Network Scaling Limits — Nonstandard Analysis Edition

A full mathematical rewrite and Lean 4 / Verso formalization of Mufan Li's 98-page [*Lecture Notes on Neural Network Scaling Limits*](https://mufan-li.github.io/files/Lecture%20Notes/nn_scaling.pdf) (STAT 946, University of Waterloo) using **Robinson's Nonstandard Analysis** and **Loeb Probability Spaces**.

* **Compiled Monograph PDF:** [`pdf/nn_scaling_nsa.pdf`](pdf/nn_scaling_nsa.pdf) (108 pages, complete Chapters 1–6, Notation, Appendix A, Exercises, Figures, Tables, and Bibliography)
* **Coverage Matrix:** [`COVERAGE.md`](COVERAGE.md)
* **Design Specification:** [`SPEC.md`](SPEC.md)

---

## Core Idea

Instead of juggling nested sequential limits ($\lim_{d\to\infty}\lim_{n\to\infty}$ vs. $\lim_{d/n\to\bar{\tau}}$, $O_{\mathbb{P}}(n^{-1/2})$ remainders, Skorohod tightness sequences, and Wasserstein compactness arguments), we fix a single $\aleph_1$-saturated nonstandard enlargement $({}^*\mathbb{R}, {}^*\mathbb{N})$ and work directly with **concrete hyperfinite neural networks** of unlimited width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$, depth $D \in {}^*\mathbb{N}\setminus\mathbb{N}$, or dataset size $M \in {}^*\mathbb{N}\setminus\mathbb{N}$:

* **Scale hierarchy as ring theory:** Asymptotic rates $O(1)$, $o(1)$, and $\Theta(1)$ become exact algebraic membership in the ring of **limited hyperreals** $\mathbb{L}$, its maximal ideal of **infinitesimals** $\mathbb{I}$ ($x \approx y$), and the multiplicative group of **appreciable hyperreals** $\mathbb{A} = \mathbb{L}\setminus\mathbb{I}$ ($x \asymp y$).
* **Distributional and process limits as standard parts:** On the Loeb probability space $(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))$, NNGP/NTK concentration, double-descent Wishart risk, McKean–Vlasov propagation of chaos, and Keisler–Lindstrøm neural covariance SDEs arise by applying the ring homomorphism $\operatorname{st} : \mathbb{L} \to \mathbb{R}$ to exact hyperfinite identities.
* **Faithful prose preservation:** Mufan Li's exposition, motivation, remarks, numbering, figures, tables, and exercises are preserved as closely as possible; only the mathematical apparatus is translated into nonstandard analysis.

---

## Repository Layout

```text
nn-scaling-nsa/
├── pdf/
│   └── nn_scaling_nsa.pdf              # Compiled 108-page Stage 1 NSA monograph
├── tex/
│   ├── main.tex                        # Top-level LaTeX report entry point
│   ├── preamble.tex                    # Theorem counters + hyperreal/Loeb macros
│   ├── ch01_intro.tex                  # Ch 1: Scaling laws, CLT, Wigner semicircle
│   ├── notation.tex                    # Standard + NSA notation table
│   ├── ch02_kernels.tex                # Ch 2: Shallow/deep NNGP & NTK lazy regime
│   ├── ch03_double_descent.tex         # Ch 3: Random-projection double descent
│   ├── ch04_feature_learning.tex       # Ch 4: Mean-field PDE, Wasserstein flow, μP, DMFT
│   ├── ch05_depth_sde.tex              # Ch 5: ResNet ODE/SDE & shaped covariance SDEs
│   ├── ch06_proportional_topics.tex    # Ch 6: Shaped attention, Dyson BM, Burgers, 1-step FL
│   ├── appa_technical.tex              # App A: Loeb weak shadows, SPD(m) BM, conditioning
│   ├── acknowledgements.tex            # Credits & editorial note
│   ├── refs.bib                        # Original + NSA bibliography
│   └── figures/                        # Reproducible vector PDF plots
├── NNScaling/
│   ├── Foundations.lean                # ℝ* scale algebra (𝕃, 𝕀, 𝔸, st) & Loeb interfaces
│   ├── Ch01_Introduction.lean          # Hyperfinite scaling microscope, CLT, semicircle
│   ├── Ch02_Kernels.lean               # Gram PSD, Cho–Saul, NTK dissipation & displacement
│   ├── Ch03_DoubleDescent.lean         # Hyperfinite Wishart st & Exercises 3.4.1–3.4.2
│   ├── Ch04_FeatureLearning.lean       # μP exponent uniqueness & hyperreal scale theorem
│   ├── Ch05_DepthSDE.lean              # Isserlis/Wick tensor, GBM drifts, blowup ODE
│   ├── Ch06_ProportionalTopics.lean    # Shaped attention, SPD congruence, Burgers, overlaps
│   └── AppendixA_Technical.lean        # Cometric duals & 4-block projector orthogonality
├── NNScaling.lean                      # Verso literate landing page
├── scripts/
│   └── gen_figures.py                  # Reproducible vector figures (uv + matplotlib/scipy)
├── SPEC.md                             # Architectural specification
└── COVERAGE.md                         # Complete monograph-to-Lean coverage table
```

---

## Building Locally

### 1. Lean 4 + Verso Literate Site (`v4.35.0`)

```bash
lake build
lake query :literateHtml
```

Every Lean module compiles with `autoImplicit = false`, **zero** custom axioms, and **zero** `sorry` placeholders.

### 2. LaTeX Monograph (`pdf/nn_scaling_nsa.pdf`)

```bash
uv run --with matplotlib --with numpy --with scipy python3 scripts/gen_figures.py
cd tex && latexmk -pdf -interaction=nonstopmode -outdir=build main.tex
cp build/main.pdf ../pdf/nn_scaling_nsa.pdf
```

---

## Attribution

Based on Mufan Li's *Lecture Notes on Neural Network Scaling Limits* (STAT 946, University of Waterloo, 2026). Nonstandard Analysis edition and Lean 4 / Verso formalization by Alok Singh.
