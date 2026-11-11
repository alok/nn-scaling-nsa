# Developer Guide: Rewriting & Formalizing Neural Network Scaling Limits via Nonstandard Clifford Analysis

> **Purpose of this guide:** This document is a self-contained, from-scratch manual for an engineer or mathematician who wants to understand, re-derive, and code every piece of `nn-scaling-nsa` by hand — without relying on black-box automation. It covers the surrounding deep-learning scaling theory, the mathematical machinery of Robinson's Nonstandard Analysis + Loeb measure (Stage 1), the synthesis with Geometric / Clifford / Dirac Analysis (Stage 2), the Lean 4 + Mathlib `Hyperreal` and `CliffordAlgebra` internals, the Verso literate-programming pipeline, and the two-stage Jujutsu (`jj`) commit-curation workflow.

---

## Table of Contents

1. [Architectural Big Picture & Why Two Stages?](#1-architectural-big-picture--why-two-stages)
2. [Surrounding Context: The Landscape of Neural Network Scaling Limits](#2-surrounding-context-the-landscape-of-neural-network-scaling-limits)
3. [Stage 1 Deep Dive: Robinson's Enlargement, Loeb Probability, & Keisler SDEs](#3-stage-1-deep-dive-robinsons-enlargement-loeb-probability--keisler-sdes)
   - 3.1 [Why Classical Scaling Proofs Feel Repetitive](#31-why-classical-scaling-proofs-feel-repetitive)
   - 3.2 [The Hyperreal Valuation Ring $(\mathbb{L}, \mathbb{I}, \mathbb{A})$ as an Asymptotic Type System](#32-the-hyperreal-valuation-ring-mathbbl-mathbbi-mathbba-as-an-asymptotic-type-system)
   - 3.3 [Transfer Principle vs. Standard Part: The Fundamental Discipline](#33-transfer-principle-vs-standard-part-the-fundamental-discipline)
   - 3.4 [Loeb Measure & Why Internal $\sigma$-Additivity Fails](#34-loeb-measure--why-internal-sigma-additivity-fails)
   - 3.5 [Anderson's Hyperfinite Random Walk & Keisler–Lindstrøm SDEs](#35-andersons-hyperfinite-random-walk--keislerlindstrøm-sdes)
   - 3.6 [Depth–Width Galaxies & Non-Commuting Limits via Overspill](#36-depthwidth-galaxies--non-commuting-limits-via-overspill)
4. [Stage 2 Deep Dive: Nonstandard Clifford & Dirac Analysis](#4-stage-2-deep-dive-nonstandard-clifford--dirac-analysis)
   - 4.1 [Why Layer Clifford Algebra on Top of Nonstandard Analysis?](#41-why-layer-clifford-algebra-on-top-of-nonstandard-analysis)
   - 4.2 [Notation Hygiene: Why Reversion Must Be $M^{\sim}$ Instead of $\widetilde{M}$](#42-notation-hygiene-why-reversion-must-be-msim-instead-of-widetildem)
   - 4.3 [Pillar I: Scalar-Grade Gram Kernels vs. Antisymmetric Bivector Curl](#43-pillar-i-scalar-grade-gram-kernels-vs-antisymmetric-bivector-curl)
   - 4.4 [Pillar II: Unit Bivectors $\hat{B}^2 = -1$ Across Chapters 1, 2, & 6](#44-pillar-ii-unit-bivectors-hatb2---1-across-chapters-1-2--6)
   - 4.5 [Pillar III: Hestenes Blade Projections & Wedge-Volume Double Descent](#45-pillar-iii-hestenes-blade-projections--wedge-volume-double-descent)
   - 4.6 [Pillar IV: Parameter Dirac Operators & Monogenic Otto–Wasserstein Flow](#46-pillar-iv-parameter-dirac-operators--monogenic-ottowasserstein-flow)
   - 4.7 [Pillar V: Deriving Dyson Eigenvalue Repulsion from $\operatorname{Spin}(m)$](#47-pillar-v-deriving-dyson-eigenvalue-repulsion-from-operatorname-spinm)
5. [Coding the Lean 4 + Mathlib Formalization from Scratch](#5-coding-the-lean-4--mathlib-formalization-from-scratch)
   - 5.1 [How Mathlib Constructs `Hyperreal` ($\mathbb{R}^*$ = Germ over an Ultrafilter)](#51-how-mathlib-constructs-hyperreal-mathbbr--germ-over-an-ultrafilter)
   - 5.2 [Building `st : ℝ* → ℝ` via Dedekind `sSup` Without Choosing Noncomputable Witness Axioms](#52-building-st---via-dedekind-ssup-without-choosing-noncomputable-witness-axioms)
   - 5.3 [Packaging `LimitedSubring`, `InfinitesimalIdeal`, and `stRingHom`](#53-packaging-limitedsubring-infinitesimalideal-and-stringhom)
   - 5.4 [How Mathlib Constructs `CliffordAlgebra Q` and `contractLeft`](#54-how-mathlib-constructs-cliffordalgebra-q-and-contractleft)
   - 5.5 [Engineering `stCliffordHom` Without Typeclass Diamonds (`RingHom.toAlgebra'`)](#55-engineering-stcliffordhom-without-typeclass-diamonds-ringhomtoalgebra)
   - 5.6 [Lean 4 `v4.35.0` & Verso Gotchas You Will Hit If Coding Manually](#56-lean-4-v4350--verso-gotchas-you-will-hit-if-coding-manually)
6. [LaTeX Monograph & Reproducible Figure Pipeline](#6-latex-monograph--reproducible-figure-pipeline)
7. [Two-Stage Jujutsu (`jj`) History Curation Workflow](#7-two-stage-jujutsu-jj-history-curation-workflow)
8. [Step-by-Step Manual Reconstruction Exercises](#8-step-by-step-manual-reconstruction-exercises)

---

## 1. Architectural Big Picture & Why Two Stages?

Mufan Li's 98-page *Lecture Notes on Neural Network Scaling Limits* (STAT 946, University of Waterloo) unifies six major threads of modern deep-learning theory:
1. Empirical compute/parameter scaling laws and classical limit prototypes (CLT, Wigner semicircle, McKean–Vlasov particles);
2. Infinite-width Gaussian Process (NNGP) and lazy Neural Tangent Kernel (NTK) limits;
3. High-dimensional random-projection double descent;
4. Mean-field continuity PDEs, Otto–Wasserstein gradient flows, Maximal Update Parameterization ($\mu$P), and Dynamical Mean-Field Theory (DMFT);
5. Infinite-depth ODE/SDE limits and proportional depth–width neural covariance SDEs;
6. Shaped Transformers, Geometric Dyson Brownian Motion, Burgers spectral fixed points, and proportional-regime feature learning.

When rewriting a monograph of this breadth under two distinct mathematical lenses — **Nonstandard Analysis (NSA)** and **Clifford / Geometric Analysis** — mixing both lenses simultaneously from commit 1 creates conceptual muddiness: a reader cannot tell which simplifications came from hyperfinite infinitesimals and which came from multivector algebra.

We therefore enforce a **strict linear two-stage architecture**:

```
root() ──► [9 atomic commits: Stage 1 Pure NSA] ──► bookmark `nsa` (pdf/nn_scaling_nsa.pdf)
                                                          │
                                                          ▼
           [7 atomic commits: Stage 2 Clifford] ──► bookmark `main` (pdf/nn_scaling_clifford.pdf)
```

1. **Stage 1 (`::nsa`)** keeps Mufan Li's linear-algebraic objects (inner products $\langle u, v\rangle$, orthogonal projectors $P_\phi$, Euclidean gradients $\nabla_\theta f$) intact and changes *only* the limit machinery to Robinson's enlargement $({}^*\mathbb{R}, {}^*\mathbb{N})$ and Loeb probability spaces.
2. **Stage 2 (`nsa..main`)** preserves the entire nonstandard backbone of Stage 1 and upgrades the *geometric* primitives to Clifford algebras $\mathcal{C}\ell_n(\mathbb{R})$, $\mathcal{C}\ell_n(\mathbb{L})$, and ${}^*\mathcal{C}\ell_N$. Running `git diff nsa..main` isolates the exact mathematical contribution of Clifford Analysis line by line.

---

## 2. Surrounding Context: The Landscape of Neural Network Scaling Limits

Every scaling limit in deep learning chooses **which architectural integers become unlimited** and **how weights and learning rates scale with them**:

| Regime | Unlimited Hypernaturals | Weight / Readout Scale | Learning Rate $\eta$ | Internal Feature Shift $\frac{1}{N}\lVert\Delta h_\ell\rVert^2$ | Limiting Object |
|---|---|---|---|---|---|
| **NNGP (Ch 2.1–2.2)** | Width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$ ($d, m$ standard) | $1/\sqrt{N}$ readout | $\eta = 0$ (init) | $0$ | Gaussian Process $\operatorname{GP}(0, \Phi_d)$ |
| **NTK / Lazy (Ch 2.3–2.5)** | Width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$ ($d, m$ standard) | $1/\sqrt{N}$ readout (NTP) | $\eta \asymp 1$ | $\mathcal{O}(N^{-1}) \subset \mathbb{I}$ (infinitesimal) | Linear ODE $\partial_t r = -\frac{1}{m} K r$ |
| **Double Descent (Ch 3)** | $(M, N_0, N) \in ({}^*\mathbb{N}\setminus\mathbb{N})^3$, $\operatorname{st}(N_0/M)=\gamma$, $\operatorname{st}(N/M)=\delta$ | Ridgeless $Z^\dagger y$ | Closed-form | Fixed random features | 3-phase Marchenko–Pastur / Wishart risk |
| **Mean Field / $\mu$P (Ch 4)** | Width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$ ($d, m$ standard) | $1/N$ readout ($\gamma_N = \sqrt{N}$) | $\eta_N \asymp N$ | $\in \mathbb{A}$ (appreciable!) | Continuity PDE / DMFT |
| **ResNet ODE/SDE (Ch 5.1–5.2)** | Depth $D \in {}^*\mathbb{N}\setminus\mathbb{N}$ | Branch scale $1/D$ or $1/\sqrt{D}$ | Init | Step $\Delta\tau = 1/D \in \mathbb{I}$ | Neural ODE / Itô SDE |
| **Proportional Depth–Width (Ch 5.3–Ch 6)** | $(D, N) \in ({}^*\mathbb{N}\setminus\mathbb{N})^2$, $\operatorname{st}(D/N) = \bar{\tau} \in \mathbb{A}_+$ | Kaiming / $N^{-1/2}$-shaped | Init or 1-step SGD | Fluctuation $\mathcal{O}(N^{-1/2})$ per layer | Covariance SDE / Dyson BM / Burgers PDE |

In standard analysis, moving from row to row requires completely different topological machinery: characteristic functions + Kolmogorov–Chentsov tightness in Ch 2, Marchenko–Pastur / Wishart matrix limits in Ch 3, Wasserstein-2 compactness + McKean–Vlasov coupling in Ch 4, and Skorohod $J_1$ tightness + Stroock–Varadhan martingale problems in Ch 5–6.

In **Nonstandard Analysis**, all six rows live inside **one fixed hyperfinite network** at fixed $(N, D, M)$, and every limit is extracted by **one map**: the standard-part ring homomorphism $\operatorname{st} : \mathbb{L} \to \mathbb{R}$.

---

## 3. Stage 1 Deep Dive: Robinson's Enlargement, Loeb Probability, & Keisler SDEs

### 3.1 Why Classical Scaling Proofs Feel Repetitive

A classical scaling proof has to do two jobs at the same time:
1. **Algebraic/probabilistic calculation at finite size $n$**: e.g., conditioning a Gaussian matrix, expanding Softmax to second order, or applying Isserlis' fourth-moment formula;
2. **$\varepsilon$–$\delta$ / tightness bookkeeping across $n = 1, 2, \dots$**: e.g., choosing truncation thresholds $R_n \to \infty$, tracking $o_{\mathbb{P}}(n^{-1/2})$ remainders, shifting jump times via homeomorphisms $\lambda_n \in \Lambda_T$ for Skorohod $J_1$, and passing to convergent subsequences via Prokhorov's theorem.

Job 1 contains 100% of the deep-learning insight; Job 2 accounts for 70% of the page count. Nonstandard Analysis eliminates Job 2's sequential boilerplate by working at a single unlimited hypernatural $N \in {}^*\mathbb{N} \setminus \mathbb{N}$ inside an $\aleph_1$-saturated enlargement.

### 3.2 The Hyperreal Valuation Ring $(\mathbb{L}, \mathbb{I}, \mathbb{A})$ as an Asymptotic Type System

Inside the ordered field ${}^*\mathbb{R}$, elements stratify algebraically relative to the embedded standard reals $\mathbb{R} \hookrightarrow {}^*\mathbb{R}$:

* **Limited (finite) hyperreals** $\mathbb{L} := \{x \in {}^*\mathbb{R} : \exists r \in \mathbb{R},\; \lvert x\rvert < r\}$ — a **valuation subring** of ${}^*\mathbb{R}$. Replaces $O(1)$.
* **Infinitesimals** $\mathbb{I} := \{x \in {}^*\mathbb{R} : \forall r \in \mathbb{R}_{>0},\; \lvert x\rvert < r\}$ — the **unique maximal ideal** of $\mathbb{L}$ ($\mathbb{L} \cdot \mathbb{I} \subseteq \mathbb{I}$). Defines infinite closeness $x \approx y \iff x - y \in \mathbb{I}$. Replaces $o(1)$.
* **Appreciable hyperreals** $\mathbb{A} := \mathbb{L} \setminus \mathbb{I} = \mathbb{L}^\times$ — the **group of units** of $\mathbb{L}$! Every $x \in \mathbb{A}$ is invertible inside $\mathbb{L}$ ($x^{-1} \in \mathbb{A}$). Defines exact scale equivalence $x \asymp y \iff x/y \in \mathbb{A}$. Replaces $\Theta(1)$.
* **Unlimited hyperreals** ${}^*\mathbb{R} \setminus \mathbb{L}$ — reciprocals of nonzero infinitesimals ($(x \in {}^*\mathbb{R}\setminus\mathbb{L}) \iff x^{-1} \in \mathbb{I}\setminus\{0\}$). Replaces $\to \infty$.

By Dedekind completeness of $\mathbb{R}$, every $x \in \mathbb{L}$ sits infinitely close to a unique standard real $\operatorname{st}(x) := \sup\{r \in \mathbb{R} : r < x\} \in \mathbb{R}$, giving the fundamental short exact sequence of commutative rings:

$$0 \longrightarrow \mathbb{I} \longrightarrow \mathbb{L} \xrightarrow{\;\operatorname{st}\;} \mathbb{R} \longrightarrow 0.$$

Why does this simplify neural network scaling proofs? Consider **Maximal Update ($\mu$P)** in Chapter 4 (`hyperreal_mup_scale_solution` in `NNScaling/Ch04_FeatureLearning.lean`):
* Feature learning requires $\eta_N / (\gamma_N \sqrt{N}) \in \mathbb{A}$.
* Non-exploding, non-vanishing output evolution requires $\eta_N / \gamma_N^2 \in \mathbb{A}$.
* Because $\mathbb{A} = \mathbb{L}^\times$ is a **multiplicative group**, dividing the first unit by the second immediately gives $\gamma_N / \sqrt{N} \in \mathbb{A}$ ($\gamma_N \asymp \sqrt{N}$), and multiplying back gives $\eta_N / N \in \mathbb{A}$ ($\eta_N \asymp N$)! No limits, no `limsup`/`liminf`, just group closure of $\mathbb{L}^\times$.

### 3.3 Transfer Principle vs. Standard Part: The Fundamental Discipline

When writing NSA proofs manually, there is **one golden rule** you must never violate:

> **The Transfer Principle applies ONLY to internal first-order formulas** (formulas that do NOT mention $\mathbb{L}$, $\mathbb{I}$, $\mathbb{A}$, $\approx$, $\operatorname{st}$, or $L({}^*\mathbb{P})$). External predicates like "$x$ is limited" are NOT internal sets — if $\{n \in {}^*\mathbb{N} : n \in \mathbb{N}\}$ were internal, it would have no least upper bound, violating internal induction!

Conversely, that very failure of internalness gives you **Robinson's Overspill Principle**:
* If an internal formula $\psi(n)$ holds for every standard $n \in \mathbb{N}$, the internal set $\{n \in {}^*\mathbb{N} : \forall k \le n,\, \psi(k)\}$ contains $\mathbb{N}$; since $\mathbb{N}$ is not internal, it must *overspill* to some unlimited $N_0 \in {}^*\mathbb{N} \setminus \mathbb{N}$!

Therefore every proof in the monograph follows a crisp **two-phase pipeline**:
1. **Internal Phase (Transfer):** Apply exact finite-dimensional theorems (Gaussian conditioning, Moore–Penrose pseudoinverses, Isserlis' theorem, Doob's maximal inequality, Taylor's theorem with Lagrange remainder, Hadamard's eigenvalue perturbation) to the width-$N$ internal network over ${}^*\mathbb{R}$.
2. **External Phase (Loeb Shadow):** Bound the internal remainder in $\mathbb{I}$ (using Markov/Chebyshev/S-integrability) and apply $\operatorname{st}$ once at the end!

### 3.4 Loeb Measure & Why Internal $\sigma$-Additivity Fails

At unlimited width $N \in {}^*\mathbb{N}\setminus\mathbb{N}$, the internal probability ${}^*\mathbb{P} : \mathcal{A} \to {}^*[0, 1]$ takes values in ${}^*[0, 1]$ and is only *internally* finitely/hyper-finitely additive — not countably additive on external countable unions!

Peter Loeb's 1975 breakthrough (`Loeb 1975`) converts $(\Omega, \mathcal{A}, {}^*\mathbb{P})$ into a genuine standard Kolmogorov probability space $(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))$:
1. Define the finitely additive real-valued pre-measure $\mu_0(A) := \operatorname{st}({}^*\mathbb{P}(A)) \in [0, 1]$ for $A \in \mathcal{A}$.
2. Why is $\mu_0$ automatically countably additive on $\mathcal{A}$ whenever $A = \bigsqcup_{k=1}^\infty A_k$ happens to lie in $\mathcal{A}$? By $\aleph_1$-saturation! If $A_k \in \mathcal{A}$ are pairwise disjoint and $\bigsqcup_{k=1}^\infty A_k = A \in \mathcal{A}$, the nested nonempty internal sets $B_m := A \setminus \bigsqcup_{k=1}^m A_k$ would have nonempty intersection if every $B_m \neq \varnothing$, contradicting $\bigcap_{m=1}^\infty B_m = \varnothing$! Thus $A_k = \varnothing$ for all sufficiently large $k$, making countable additivity on $\mathcal{A}$ trivial!
3. Carathéodory's extension theorem then extends $\mu_0$ uniquely to the $\sigma$-algebra completion $\mathcal{L}(\mathcal{A})$, producing the **Loeb measure** $L({}^*\mathbb{P})$.

Watch out for **S-integrability** (highlighted explicitly in Section 5.3 of the monograph!):
* In a deep linear network at fixed width $n$ and unlimited depth $D \in {}^*\mathbb{N}\setminus\mathbb{N}$ ($N/D \approx 0$), the internal expectation satisfies ${}^*\mathbb{E}[\Phi_D] = \Phi_0 > 0$, yet $\operatorname{st}(\Phi_D) = 0$ $L({}^*\mathbb{P})$-almost surely ($\mathbb{E}_{L({}^*\mathbb{P})}[\operatorname{st}(\Phi_D)] = 0 \neq \operatorname{st}({}^*\mathbb{E}[\Phi_D])$)!
* Why? An internal event of infinitesimal probability ${}^*\mathbb{P}(E) \approx 0$ carries exponentially unlimited values $\Phi_D \in {}^*\mathbb{R}\setminus\mathbb{L}$ whose product ${}^*\mathbb{P}(E) \cdot \Phi_D$ stays appreciable! Passing $\operatorname{st}$ inside ${}^*\mathbb{E}[\cdot]$ requires uniform integrability (e.g., a standard bounded higher moment ${}^*\mathbb{E}[\lvert X\rvert^p] \in \mathbb{L}$ for standard $p > 1$).

### 3.5 Anderson's Hyperfinite Random Walk & Keisler–Lindstrøm SDEs

In Chapters 5 and 6, a layer-indexed Markov chain $\Phi_0, \Phi_1, \dots, \Phi_{\lfloor NT \rfloor}$ with infinitesimal step $\Delta\tau = 1/N \approx 0$ becomes a continuous-time diffusion without ever invoking Prokhorov's theorem or shifting jump times in Skorohod space:

* **Why Skorohod time-warping disappears (`Appendix A.3`):** On $D([0, T], S)$, $J_1$-convergence to a *continuous* limit $x \in C([0, T], S)$ is equivalent to uniform convergence. Nonstandardly, an internal piecewise-constant path $X_{\lfloor Nt \rfloor}^{(N)}$ has continuous shadow $x$ if and only if it is nearstandard and **S-continuous**:
  $$s \approx t \text{ in } {}^*[0, T] \implies X_{\lfloor Ns \rfloor}^{(N)} \approx X_{\lfloor Nt \rfloor}^{(N)}.$$
* **Keisler–Lindstrøm Moment Matching (`Theorem A.4`):** Decompose one layer step $\Delta X_\ell = X_{\ell+1}^{(N)} - X_\ell^{(N)}$ on a compact localization domain ${}^*K$ into predictable drift plus martingale increment:
  1. Drift rate $\frac{1}{\Delta\tau}{}^*\mathbb{E}[\Delta X_\ell \mid \mathcal{F}_\ell] \approx {}^*b(X_\ell^{(N)})$ gives a cumulative drift sum with bounded difference quotients — automatically S-continuous!
  2. Covariance rate $\frac{1}{\Delta\tau}{}^*\!\operatorname{Cov}(\Delta X_\ell \mid \mathcal{F}_\ell) \approx {}^*\Sigma(X_\ell^{(N)})$ and infinitesimal cubic jump rate $\frac{1}{\Delta\tau}{}^*\mathbb{E}[\lVert\Delta X_\ell\rVert^3 \mid \mathcal{F}_\ell] \approx 0$ imply (by Markov's inequality $\frac{1}{\Delta\tau}{}^*\mathbb{P}(\lVert\Delta X_\ell\rVert > \varepsilon) \le \varepsilon^{-3}\frac{1}{\Delta\tau}{}^*\mathbb{E}[\lVert\Delta X_\ell\rVert^3] \approx 0$) that the hyperfinite martingale has bounded quadratic variation and zero standard jumps, hence is $L({}^*\mathbb{P})$-a.s. S-continuous, and its standard part $X_t^\circ = \operatorname{st}(X_{\lfloor Nt \rfloor}^{(N)})$ solves $dX_t = b(X_t)\,dt + \sigma(X_t)\,dB_t$!

### 3.6 Depth–Width Galaxies & Non-Commuting Limits via Overspill

Figure 5.1 in Chapter 5 illustrates why $\lim_{d\to\infty}\lim_{n\to\infty} \neq \lim_{n\to\infty}\lim_{d\to\infty}$ for plain MLPs. In $(\hN)^2$, unlimited pairs $(N, D) \in ({}^*\mathbb{N}\setminus\mathbb{N})^2$ partition into three external **galaxies** according to the hyperreal ratio $D / N$:
1. **Wide galaxy ($D / N \in \mathbb{I}$):** $\log(\Phi_D/\Phi_0) \approx 0$, so $\Phi_D \approx \Phi_0 \in \mathbb{A}$ deterministically.
2. **Proportional galaxy ($D / N \in \mathbb{A}$, $\operatorname{st}(D/N) = \bar{\tau} \in (0,\infty)$):** $\operatorname{st}(\log(\Phi_D/\Phi_0)) \sim \mathcal{N}(-\bar{\tau}, 2\bar{\tau})$, so $\Phi_D \in \mathbb{A}$ $L({}^*\mathbb{P})$-a.s. with genuine randomness!
3. **Deep galaxy ($N / D \in \mathbb{I}$, $D/N \in {}^*\mathbb{R}\setminus\mathbb{L}$):** $\Phi_D \in \mathbb{I}$ $L({}^*\mathbb{P})$-a.s. (rank/norm collapse!), so $\operatorname{Loeb}(\Phi_D \in \mathbb{L}) = 1$ while $\operatorname{Loeb}(\Phi_D \in \mathbb{A}) = 0$.

Notice how Robinson's Overspill converts sequential limits into simultaneous hyperfinite regimes: if $\lim_{n\to\infty} A(n, d) = A_\infty(d)$ for each standard $d \in \mathbb{N}$ and $\lim_{d\to\infty} A_\infty(d) = A_{\infty,\infty}$, Overspill guarantees an unlimited $D(N) \in {}^*\mathbb{N}\setminus\mathbb{N}$ growing slowly enough ($D(N)/N \approx 0$, inside the wide galaxy!) that ${}^*A(N, D(N)) \approx A_{\infty,\infty}$. Non-commutativity of sequential limits is simply the geometric fact that $D/N \in \mathbb{I}$, $D/N \in \mathbb{A}$, and $N/D \in \mathbb{I}$ are disjoint subsets of $({}^*\mathbb{N}\setminus\mathbb{N})^2$.

---

## 4. Stage 2 Deep Dive: Nonstandard Clifford & Dirac Analysis

### 4.1 Why Layer Clifford Algebra on Top of Nonstandard Analysis?

Look closely at the linear-algebraic objects recurring across Mufan Li's six chapters:
1. Empirical inner products $\frac{1}{N}\langle u, v\rangle$ of activations, gradients, and key–query vectors;
2. $2\times 2$ planar rotations in Cho–Saul's ReLU expectation, complex Stieltjes kernels $(z - x)^{-1}$, and infinitesimal orthogonal frame rotations in Dyson Brownian Motion;
3. Orthogonal subspace projections $P_\phi = \phi(\phi^\top\phi)^\dagger\phi^\top$ and Schur complements $g_1^\top P_{G_2}^\perp g_1$;
4. Divergences $\nabla \cdot (v_t \rho_t)$ and curl-free potential gradients $v_t = -\eta_0 \nabla(\delta\mathcal{F}/\delta\rho)$.

In standard matrix notation, these four operations look unrelated: dot products $u^\top v$, complex numbers $i^2 = -1$, Moore–Penrose pseudoinverses $(\phi^\top\phi)^\dagger$, and vector-calculus $\nabla \cdot$ / $\nabla$.

In the **Euclidean Clifford Algebra** $\mathcal{C}\ell_n(\mathbb{R})$ (and its internal hyperfinite counterpart ${}^*\mathcal{C}\ell_N = \mathcal{C}\ell_N({}^*\mathbb{R})$), **all four are specializations of a single associative product** — the **geometric product** $uv = u \cdot v + u \wedge v$ defined by $v^2 = \lVert v\rVert^2 \cdot 1$!

### 4.2 Notation Hygiene: Why Reversion Must Be $M^{\sim}$ Instead of $\widetilde{M}$

A subtle practical trap when retrofitting Clifford algebra onto Mufan Li's notes: Mufan Li uses overhead tildes *everywhere* for probability objects — $\widetilde{W}_\ell$ (independent Gaussian weight copy in Gaussian conditioning), $\widetilde{Z}_\ell$ (unconditioned Gaussian pre-activations), $\widetilde{h}_\ell$, and $\widetilde{A}_\ell$.

In Hestenes' Geometric Algebra literature, reversion (reversing the order of vector factors: $(v_1 v_2 \cdots v_r)^{\sim} = v_r \cdots v_2 v_1$) is often written $\widetilde{M}$. Using $\widetilde{M}$ in our LaTeX preamble would create catastrophic visual ambiguity with $\widetilde{W}_\ell$! Defining `\newcommand{\rev}[1]{#1^{\sim}}` (superscript tilde $M^{\sim}$, also standard in Doran–Lasenby and Lounesto) keeps every probability tilde $\widetilde{W}_\ell$ untouched while making multivector reversion $M^{\sim}$ unmistakable.

### 4.3 Pillar I: Scalar-Grade Gram Kernels vs. Antisymmetric Bivector Curl

For any two vectors $u, v \in {}^*\mathbb{R}^N \hookrightarrow {}^*\mathcal{C}\ell_N$, since $v^{\sim} = v$:
$$u v^{\sim} = u v = \underbrace{\langle u v\rangle_0}_{\text{symmetric scalar } \langle u, v\rangle} + \underbrace{u \wedge v}_{\text{antisymmetric bivector } \in \bigwedge^2({}^*\mathbb{R}^N)}.$$

* **NNGP & Feature Gram Matrices (Chapters 2, 5, 6):** Empirical covariances $\Phi_\ell^{\alpha\beta} = \frac{1}{N}\langle h_\ell^\alpha (h_\ell^\beta)^{\sim}\rangle_0$ extract the grade-$0$ scalar part and discard the feature-plane bivector $h_\ell^\alpha \wedge h_\ell^\beta$.
* **Transformer Attention (Chapter 6.1):** Key–query products decompose in ${}^*\mathcal{C}\ell_{n_k}$ as $k^\alpha q^\beta = \langle k^\alpha q^\beta\rangle_0 + k^\alpha \wedge q^\beta$. Ordinary dot-product Softmax logits keep only the grade-$0$ scalar $\langle k^\alpha q^\beta\rangle_0$, throwing away the grade-$2$ rotational torque bivector $k^\alpha \wedge q^\beta$ that modern Clifford-equivariant attention layers (`Ruhe et al. 2023`, `Brandstetter et al. 2023`) explicitly propagate.
* **NTK vs. Bivector Curl (Chapter 2.3):** With the parameter Dirac gradient $\partial_\theta = \sum_{p=1}^{\dim(\theta)} e_p \partial_{\theta_p} \in {}^*\mathcal{C}\ell_{\dim(\theta)}$, the full geometric tangent product between inputs $\alpha$ and $\beta$ splits into:
  $$(\partial_\theta f_\alpha)^{\sim}(\partial_\theta f_\beta) = \underbrace{K_t^{(N),\alpha\beta}}_{\text{grade 0 (symmetric NTK)}} + \underbrace{\Omega_t^{(N),\alpha\beta}}_{\text{grade 2 (antisymmetric curl } \partial_\theta f_\alpha \wedge \partial_\theta f_\beta\text{)}}.$$
  Why does gradient-flow risk dissipation $\partial_t L(\theta(t)) = -\frac{1}{m^2} r^\top K_t^{(N)} r$ depend *only* on $K_t^{(N)}$? Because contracting $r_\alpha r_\beta$ against the antisymmetric bivector $\Omega_t^{(N),\alpha\beta} = -\Omega_t^{(N),\beta\alpha}$ vanishes identically (`bivector_curl_quadForm_zero` in `NNScaling/Ch02_Kernels.lean`)!

### 4.4 Pillar II: Unit Bivectors $\hat{B}^2 = -1$ Across Chapters 1, 2, & 6

Let $e_1, e_2$ be any two orthonormal vectors ($e_1^2 = e_2^2 = 1$, $e_1 e_2 = -e_2 e_1$). Their geometric product $\hat{B} := e_1 e_2 = e_1 \wedge e_2$ is a **unit 2-blade (bivector)** satisfying:
$$\hat{B}^{\sim} = e_2 e_1 = -\hat{B}, \qquad \hat{B}^2 = (e_1 e_2)(e_1 e_2) = -e_2 (e_1 e_1) e_2 = -e_2^2 = -1.$$
We prove this over **any commutative ring $R$** (`unit_bivector_sq_neg_one` in `NNScaling/Clifford.lean`). Without introducing ad hoc complex numbers $\mathbb{C}$, the even subalgebra $\mathcal{C}\ell_2^+ = \operatorname{span}\{1, \hat{B}\}$ naturally supplies geometric imaginary units across three distinct chapters:

1. **Cho–Saul ReLU Arc-Cosine Kernel (Chapter 2, Remark 2.8):** For unit inputs $u_1, u_2 \in \mathbb{R}^{n_0}$ at angle $\vartheta \in [0, \pi]$ ($\rho = \cos\vartheta$), their geometric product in $\mathcal{C}\ell_{n_0}^+$ is the **planar rotor**
   $$u_1 u_2 = \cos\vartheta + \sin\vartheta\,\hat{B} = \exp(\vartheta\,\hat{B}), \qquad (u_1 u_2)(u_1 u_2)^{\sim} = \cos^2\vartheta + \sin^2\vartheta = 1.$$
   Integrating $\max(w \cdot u_1, 0)\max(w \cdot u_2, 0)$ over the isotropic Gaussian $w \sim \mathcal{N}(0, I_{n_0})$ reduces immediately to integrating over the 2D rotor plane spanned by $\hat{B}$, yielding $J_1(\vartheta) = \sin\vartheta + (\pi - \vartheta)\cos\vartheta$.
2. **Cauchy–Dirac Stieltjes Resolvent (Chapter 1 Remark 1.5 & Chapter 6 Remark 6.10):** Identifying $z = x + \varepsilon\,\bm{i} \in \mathcal{C}\ell_2^+$ ($\bm{i} = e_1 e_2$, $\varepsilon \in \hR_{>0} \cap \mathbb{I}$), the resolvent kernel $(z - x')^{-1} = \frac{(z - x')^{\sim}}{(x - x')^2 + \varepsilon^2}$ is the 2D monogenic Cauchy–Dirac kernel, and Stieltjes inversion extracts the bivector grade $-\frac{1}{\pi}\operatorname{st}\langle (-\bm{i})\,{}^*g_\tau(x + \varepsilon\bm{i})\rangle_0$.

### 4.5 Pillar III: Hestenes Blade Projections & Wedge-Volume Double Descent

Suppose $\mathcal{S} \subseteq {}^*\mathbb{R}^P$ is an $r$-dimensional subspace spanned by linearly independent vectors $u_1, \dots, u_r$. Their exterior product $\bm{S} := u_1 \wedge \dots \wedge u_r \in \bigwedge^r({}^*\mathbb{R}^P) \subset {}^*\mathcal{C}\ell_P$ is a nonzero **simple $r$-blade** whose Clifford square $\bm{S}\bm{S}^{\sim} = \langle \bm{S}\bm{S}^{\sim}\rangle_0 = \det([u_i \cdot u_j]) > 0$ is a positive scalar, so $\bm{S}^{-1} = \bm{S}^{\sim} / \langle \bm{S}\bm{S}^{\sim}\rangle_0$ exists directly inside ${}^*\mathcal{C}\ell_P$!

For any vector $w \in {}^*\mathbb{R}^P$, Hestenes' fundamental identity splits the geometric product $w\bm{S}$ into a grade-$(r-1)$ **left contraction** $w \lrcorner \bm{S}$ and a grade-$(r+1)$ **exterior wedge** $w \wedge \bm{S}$:
$$w = (w \bm{S})\bm{S}^{-1} = \underbrace{(w \lrcorner \bm{S})\bm{S}^{-1}}_{P_{\mathcal{S}}(w) \in \mathcal{S}} + \underbrace{(w \wedge \bm{S})\bm{S}^{-1}}_{P_{\mathcal{S}}^\perp(w) \in \mathcal{S}^\perp}.$$

Look what happens when we apply this to **Double Descent (Chapter 3, Lemma 3.3)**:
* Let $G = [g_1, G_2] \in {}^*\mathbb{R}^{P \times Q}$ ($Q \le P$) have i.i.d. $\hNcal(0, 1)$ entries, and let $\bm{G}_2 := g_2 \wedge \dots \wedge g_Q \in \bigwedge^{Q-1}({}^*\mathbb{R}^P)$ be the $(Q-1)$-blade of the remaining columns.
* The diagonal entry $((G^\top G)^{-1})_{11} = (g_1^\top P_{G_2}^\perp g_1)^{-1}$ is the reciprocal squared norm of the rejection $(g_1 \wedge \bm{G}_2)\bm{G}_2^{-1}$, which is **the exact ratio of squared wedge volumes**:
  $$\bigl((G^\top G)^{-1}\bigr)_{11}^{-1} = \frac{\lVert g_1 \wedge \bm{G}_2\rVert^2}{\lVert \bm{G}_2\rVert^2} = \frac{\langle (g_1 \wedge \bm{G}_2)^{\sim}(g_1 \wedge \bm{G}_2)\rangle_0}{\langle \bm{G}_2^{\sim}\bm{G}_2\rangle_0} \sim \ns{\chi}_{P - Q + 1}^2!$$
* **Why does test variance explode at the interpolation threshold $M = N$ ($P = Q$)?** Geometrically, at $Q = P$, $\bm{G}_2$ is already a $(P-1)$-blade in $P$-dimensional space, so $g_1 \wedge \bm{G}_2 \in \bigwedge^P({}^*\mathbb{R}^P)$ is saturated in the **1-dimensional pseudoscalar line**! With only $P - Q + 1 = 1$ transverse degree of freedom left, $1/\ns{\chi}_1^2$ has infinite expectation, and normalized by $1/M \in \mathbb{I}$ at $M - N = O(1)$, the variance $N / (M - N - 1)$ shoots out of $\mathbb{L}$ into ${}^*\mathbb{R} \setminus \mathbb{L}$! We formalize the $n$-dimensional Lagrange–Cauchy–Binet wedge identity in `lagrange_bivector_schur_complement` (`NNScaling/Ch03_DoubleDescent.lean`).

### 4.6 Pillar IV: Parameter Dirac Operators & Monogenic Otto–Wasserstein Flow

In Chapter 4 (Mean-Field Limit), each neuron has parameter $\theta = (a, w) \in \mathbb{R}^{1 + n_0}$. Embed $\mathbb{R}^{1 + n_0} \hookrightarrow \mathcal{C}\ell_{1 + n_0}$ with orthonormal generators $\{e_a, e_1, \dots, e_{n_0}\}$ and define the **parameter-space vector Dirac operator**:
$$\partial_\theta := e_a \partial_a + \sum_{k=1}^{n_0} e_k \partial_{w_k}, \qquad \partial_\theta^2 = \Delta_{(a,w)}$$
(because $e_\mu^2 = 1$ and $e_\mu e_\nu + e_\nu e_\mu = 0$ for $\mu \neq \nu$ cancel all mixed partials!).

Acting on any vector field $v_t : \mathbb{R}^{1+n_0} \to \mathbb{R}^{1+n_0}$, the geometric product $\partial_\theta v_t$ splits by grade:
$$\partial_\theta v_t = \underbrace{\langle \partial_\theta v_t\rangle_0}_{\text{divergence } \nabla_\theta \cdot v_t} + \underbrace{\langle \partial_\theta v_t\rangle_2}_{\text{bivector curl } \partial_\theta \wedge v_t}.$$
1. The shallow mean-field continuity PDE (`Definition 4.4`) becomes $\partial_t \rho_t + \langle \partial_\theta (v_t \rho_t)\rangle_0 = 0$.
2. Because the Otto–Wasserstein velocity $v_t = -\eta_0 \partial_\theta \!\left(\frac{\delta\mathcal{F}}{\delta\rho}[\rho_t]\right)$ is a Dirac gradient of a scalar functional derivative, symmetry of mixed partials $\partial_\mu \partial_\nu \phi = \partial_\nu \partial_\mu \phi$ paired with $e_\mu e_\nu = -e_\nu e_\mu$ forces its bivector curl to vanish identically (`monogenic_gradient_bivector_curl_zero` in `NNScaling/Ch04_FeatureLearning.lean`):
   $$\langle \partial_\theta v_t\rangle_2 = \partial_\theta \wedge v_t = -\eta_0 (\partial_\theta \wedge \partial_\theta)\frac{\delta\mathcal{F}}{\delta\rho}[\rho_t] = 0!$$

### 4.7 Pillar V: Deriving Dyson Eigenvalue Repulsion from $\operatorname{Spin}(m)$

In Chapter 6 (`Theorem 6.9`), the feature covariance $\Phi_\tau \in \operatorname{SPD}(m)$ evolves under $d\Phi_\tau = \Phi_\tau^{1/2}\,dS_\tau\,\Phi_\tau^{1/2}$ with zero matrix drift, yet its ordered eigenvalues $\lambda_1(\tau) < \dots < \lambda_m(\tau)$ acquire a **positive repulsive drift** $+\sum_{j\neq i}\frac{\lambda_i\lambda_j}{\lambda_i - \lambda_j}\,d\tau$ that prevents eigenvalue collisions!

Where does that repulsion come from geometrically? Write the evolving orthonormal eigenframe $\{u_1(\tau), \dots, u_m(\tau)\}$ via a two-sided **spinor rotor** $R_\tau \in \operatorname{Spin}(m) \subset \mathcal{C}\ell_m^+$:
$$u_k(\tau) = R_\tau e_k R_\tau^{\sim}, \qquad R_\tau R_\tau^{\sim} = 1.$$
In the instantaneous eigenframe ($R_\tau = 1$), a stochastic step updates the rotor by $R_{\tau+d\tau} = \exp\!\left(\frac{1}{2}\sum_{i<j} d\omega_{ij}\,e_i \wedge e_j\right)$. Because $(e_i \wedge e_j)^2 = -1$, expanding the two-sided rotor sandwich (`planarRotor_sandwich_e1` in `NNScaling/Clifford.lean`) to second Itô order in plane $(i, j)$ gives:
$$\exp\!\left(\tfrac{1}{2}d\omega_{ij}\,e_i\wedge e_j\right) e_i \exp\!\left(-\tfrac{1}{2}d\omega_{ij}\,e_i\wedge e_j\right) = \left(1 - \tfrac{1}{2}(d\omega_{ij})^2\right)e_i - d\omega_{ij}\,e_j + o(d\tau).$$
Substituting into $\Phi_{\tau+d\tau} = \sum_k (\lambda_k + d\lambda_k) u_k(\tau+d\tau) u_k(\tau+d\tau)^\top$ yields:
* **Off-diagonal $(i, j)$ entry:** $d\Phi_{ij} = (\lambda_j - \lambda_i)\,d\omega_{ij}$, so matching $\mathbb{E}[(d\Phi_{ij})^2] = \lambda_i\lambda_j\,d\tau$ gives $(d\omega_{ij})^2 = \frac{\lambda_i\lambda_j}{(\lambda_i - \lambda_j)^2}\,d\tau$.
* **Diagonal $(i, i)$ entry:** $d\Phi_{ii} = d\lambda_i + \lambda_i\bigl(\cos^2(d\omega_{ij}) - 1\bigr) + \lambda_j\sin^2(d\omega_{ij}) = d\lambda_i - (\lambda_i - \lambda_j)(d\omega_{ij})^2 + o(d\tau)$.
* **Zero matrix drift $\mathbb{E}[d\Phi_{ii}] = 0$** immediately forces (`spin_eigenframe_repulsion_balance` in `NNScaling/Ch06_ProportionalTopics.lean`):
  $$\mathbb{E}[d\lambda_i \mid \mathcal{F}_\tau] = \sum_{j\neq i} (\lambda_i - \lambda_j)\,\mathbb{E}[(d\omega_{ij})^2] = \sum_{j\neq i} \frac{\lambda_i\lambda_j}{\lambda_i - \lambda_j}\,d\tau!$$
Eigenvalue repulsion in random matrix theory is literally the negative sign in $(e_i \wedge e_j)^2 = -1$ inside $\operatorname{Spin}(m)$!

---

## 5. Coding the Lean 4 + Mathlib Formalization from Scratch

### 5.1 How Mathlib Constructs `Hyperreal` ($\mathbb{R}^*$ = Germ over an Ultrafilter)

In Mathlib (`Mathlib.Analysis.Real.Hyperreal`), `Hyperreal` (scoped notation `ℝ*`) is defined as the **ultraproduct** of $\mathbb{R}^{\mathbb{N}}$ modulo a fixed nonprincipal ultrafilter `hyperfilter ℕ : Ultrafilter ℕ` refining the cofinite filter `Filter.cofinite`:

```lean
abbrev Hyperreal : Type := Germ (hyperfilter ℕ : Filter ℕ) ℝ
```

Because `hyperfilter ℕ` is an ultrafilter, `Germ (hyperfilter ℕ) ℝ` inherits a `LinearOrderedField ℝ*` instance automatically via Łoś's theorem on germs, and standard reals coerce into `ℝ*` via the constant-sequence coercion `(r : ℝ*)` (`Hyperreal.coe_lt_coe`, `Hyperreal.coe_add`, `Hyperreal.coe_mul`).

### 5.2 Building `st : ℝ* → ℝ` via Dedekind `sSup` Without Choosing Noncomputable Witness Axioms

When coding `NNScaling/Foundations.lean`, you have a crucial design choice: use Mathlib's built-in `Hyperreal.st` or define a clean self-contained `st` on top of `sSup`? Defining:

```lean
def st (x : ℝ*) : ℝ := sSup {r : ℝ | (r : ℝ*) < x}
```

has a massive pedagogical and proof-engineering advantage:
1. It is defined on **all** of `ℝ*` (defaulting cleanly via `Real.sSup` outside `Limited`), so `st (x + y)` never requires passing proof terms inside the function application!
2. Using `Real.isLUB_sSup`, proving the Fundamental Shadow Theorem (`Limited.infClose_st : Limited x → x ≊ (st x : ℝ*)`) takes 25 lines of elementary `linarith` (`NNScaling/Foundations.lean:217-244`).
3. Once you prove **uniqueness of shadows** (`st_eq_of_infClose : x ≊ (r : ℝ*) → st x = r`), every ring-homomorphism law (`st_add`, `st_neg`, `st_sub`, `st_mul`, `st_div`) reduces to a 5-line algebraic decomposition in `InfClose` + `ring`!

### 5.3 Packaging `LimitedSubring`, `InfinitesimalIdeal`, and `stRingHom`

In Stage 2 (`NNScaling/Clifford.lean`), we need to feed the limited hyperreals into Mathlib's `CliffordAlgebra Q`, which expects a `[CommRing R]` typeclass! Because `Limited` is closed under `0`, `1`, `+`, `-`, `*`, we promote the predicate `Limited : ℝ* → Prop` into a bona fide Mathlib `Subring ℝ*`:

```lean
def LimitedSubring : Subring ℝ* where
  carrier := {x : ℝ* | Limited x}
  mul_mem' hx hy := hx.mul hy
  one_mem' := limited_one
  add_mem' hx hy := hx.add hy
  zero_mem' := limited_zero
  neg_mem' hx := hx.neg
```

Because `Subring ℝ*` automatically carries a `CommRing LimitedSubring` instance, we immediately get:
1. `InfinitesimalIdeal : Ideal LimitedSubring` (`smul_mem'` is literally `Limited.mul_isInfinitesimal`!);
2. `stRingHom : LimitedSubring →+* ℝ` (packaging `st_one`, `st_mul`, `st_zero`, `st_add`);
3. `ker_stRingHom : RingHom.ker stRingHom = InfinitesimalIdeal` — a 9-line proof using `Limited.infClose_st` and `IsInfinitesimal.st_eq_zero`!

### 5.4 How Mathlib Constructs `CliffordAlgebra Q` and `contractLeft`

In Mathlib (`Mathlib.LinearAlgebra.CliffordAlgebra.Basic`), for any `[CommRing R] [AddCommGroup M] [Module R M]` and `Q : QuadraticForm R M`:
* `CliffordAlgebra Q` is constructed as the quotient of `TensorAlgebra R M` by the ring congruence generated by `ι m * ι m = algebraMap R _ (Q m)`.
* Its universal property is an **equivalence** `CliffordAlgebra.lift Q : { f : M →ₗ[R] A // ∀ m, f m * f m = algebraMap R A (Q m) } ≃ (CliffordAlgebra Q →ₐ[R] A)`.
* Grade reversion `CliffordAlgebra.reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q` is defined by lifting `ι Q` into the **opposite algebra** `(CliffordAlgebra Q)ᵐᵒᵖ` (`reverseOp`) and unwrapping `MulOpposite`! That is why `reverse (a * b) = reverse b * reverse a` (`reverse.map_mul`) is definitionally `op_injective (map_mul reverseOp a b)`.
* Hestenes' left contraction `CliffordAlgebra.contractLeft : Module.Dual R M →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q` (`Mathlib.LinearAlgebra.CliffordAlgebra.Contraction`) is constructed via `foldr'` using the graded derivation auxiliary map `x ↦ d m • x - ι Q m * fx`, giving `CliffordAlgebra.contractLeft_ι_mul d a b : contractLeft d (ι Q a * b) = d a • b - ι Q a * contractLeft d b`.

### 5.5 Engineering `stCliffordHom` Without Typeclass Diamonds (`RingHom.toAlgebra'`)

Here is the trickiest Lean 4 engineering problem in `NNScaling/Clifford.lean` — and the clean pattern you should reuse in any Lean 4 algebra project:

**Problem:** We want a ring homomorphism
$$\operatorname{st}_{\mathcal{C}\ell} : \mathcal{C}\ell_n(\mathbb{L}) \longrightarrow \mathcal{C}\ell_n(\mathbb{R})$$
mapping $\iota(v) \mapsto \iota(\operatorname{st} \circ v)$ and $c \cdot 1 \mapsto \operatorname{st}(c) \cdot 1$. However:
* `CliffordAlgebra.lift Q₁` requires the target `A = CliffordAlgebra Q₂` to be an **`R`-algebra** (`[Algebra LimitedSubring (CliffordAlgebra Q₂)]`)!
* `CliffordAlgebra Q₂` is a **noncommutative** ring (`Ring`, not `CommRing`), so `RingHom.toAlgebra` does NOT apply to `LimitedSubring →+* CliffordAlgebra Q₂`!
* Worse, registering a global `instance : Algebra LimitedSubring ℝ` could create typeclass diamonds whenever `ℝ` and `ℝ*` interact!

**Solution (`cliffordChangeRingHom` in `NNScaling/Clifford.lean:274-332`):**
Mathlib provides `RingHom.toAlgebra' (i : R →+* A) (h : ∀ c x, i c * x = x * i c) : Algebra R A`, which equips a **noncommutative** ring `A` with an `Algebra R A` structure as long as `i(R)` lands in the center of `A`!
Since `(algebraMap S (CliffordAlgebra Q₂)).comp φ` lands in the `S`-scalar center of `CliffordAlgebra Q₂`, `Algebra.commutes (φ c) x` proves centrality in one term! Scoping it via `letI` *inside* `cliffordChangeRingHom` (and `let _ : Algebra ...` inside the `@[simp]` lemmas) constructs a pure `RingHom` `CliffordAlgebra Q₁ →+* CliffordAlgebra Q₂` with **zero global instances and zero diamonds**!

### 5.6 Lean 4 `v4.35.0` & Verso Gotchas You Will Hit If Coding Manually

If you code or extend this repo manually, watch out for these five sharp edges:

1. **NEVER name a bound variable `ε` when `open scoped Hyperreal` is active!**
   Mathlib's `Hyperreal` namespace defines scoped notation `ε` for the canonical positive infinitesimal `[n ↦ 1/(n+1)]`. Writing `intro ε hε` or `fun ε => ...` causes cryptic parser/elaborator errors because `ε` parses as the constant `Hyperreal.epsilon`! Use `e`, `δ`, `rem`, or `η` instead.
2. **NEVER name a bound variable starting with `λ`!**
   In Lean 4, `λ` is the reserved lambda-abstraction token (`fun`). Writing `{λ : ℝ}` or `{λi : ℝ}` fails at parse time (`unexpected token 'λ'`). Use `lam`, `lami`, or `«λ»` in guillemets.
3. **`doc.verso = true` requires explicit roles on EVERY code span in docstrings!**
   Because `lakefile.toml` enables `doc.verso = true` for Verso literate HTML generation, writing bare `` `Limited` `` in a `/-- ... -/` or `/-! ... -/` comment triggers a Verso docstring warning/error. Always annotate code spans as `{lit}\`Limited\`` (literal code) or `{name}\`CliffordAlgebra.lift\`` (resolved Lean declaration link), and write inline math as `` $`x \approx y` `` and display math as `` $$`...` ``.
4. **Linter `linter.style.haveILetI` on `Prop` goals:**
   In Lean `v4.35.0` + Mathlib, using `letI : Algebra R A := ...` inside a `def` returning data (like `RingHom`) is required so the instance is inlined transparently, *but* using `letI` inside a `theorem` (whose return type is a `Prop`) triggers a style warning because proof irrelevance makes inlining unnecessary. Inside `theorem` proofs, write `let _ : Algebra R A := ...` instead!
5. **Customizing Verso GitHub Actions workflows:**
   Verso checks `.github/workflows/verso-literate-pages.yml` against its stock template and emits a warning if you customize it (e.g., to bundle `pdf/*.pdf` into `_site/pdf/`). Naming our custom workflow `.github/workflows/deploy-pages.yml` silences that check cleanly while deploying both the Verso literate HTML and both compiled PDFs.

---

## 6. LaTeX Monograph & Reproducible Figure Pipeline

* **Vector Figures (`scripts/gen_figures.py`):** Run via `uv run --with matplotlib --with numpy --with scipy python3 scripts/gen_figures.py`. Generates publication-quality PDF plots (`tex/figures/fig1_2_scaling.pdf`, `fig1_3_clt_berry_esseen.pdf`, `fig3_1_double_descent.pdf`), including exact characteristic-function Fourier inversion for the centered $\mathrm{Exp}(1)$ finite-$n$ CDF vs. $\mathcal{N}(0, 1)$ in Figure 1.3.
* **Multi-page Notation Table (`tex/notation.tex`):** Uses `xltabular` (`tabularx` + `longtable`) so adding NSA and Clifford notation rows breaks cleanly across pages with zero `Overfull \vbox` warnings.
* **Titlepage Hyperref Anchors (`tex/main.tex`):** Wraps `\begin{titlepage}...\end{titlepage}` with `\hypersetup{pageanchor=false}` / `\hypersetup{pageanchor=true}` so PDF page 1 and chapter page 1 never collide on `name{page.1}`.
* **Dual PDF Preservation (`pdf/`):**
  * `pdf/nn_scaling_nsa.pdf` (108 pages) is built from `nsa` and preserved untouched on `main`.
  * `pdf/nn_scaling_clifford.pdf` (111 pages) is built from `main` via `./scripts/build_pdfs.sh clifford`.

---

## 7. Two-Stage Jujutsu (`jj`) History Curation Workflow

Working directly in Jujutsu (`jj`) lets you iterate fast with messy `wip(...)` checkpoints while compiling LaTeX and debugging Lean proofs, and then rewrite each stage into a clean sequence of atomic narrative commits *after* all checks pass:

1. **Snapshot size cap for PDFs:** Compiled monographs exceed Jujutsu's default 1 MiB new-file cap (~1.01–1.12 MiB). Configure once per repo:
   ```bash
   jj config set --repo snapshot.max-new-file-size 10485760
   ```
2. **Stage isolation:** Once Stage 1 was split into 9 atomic commits and pushed to `origin` under bookmark `nsa`, `::nsa` became immutable history. Notice that if you commit while a bookmark sits on `@`, `jj` advances that bookmark; pinning `jj bookmark set nsa -r <stage1-tip> --allow-backwards` locks `nsa` permanently to Stage 1 while you work on children of `nsa`.
3. **Non-interactive history splitting:** Never run interactive `jj split` or `jj squash -i` in scripts. Instead:
   * Create a fresh empty working copy directly on top of the base bookmark (`jj new nsa`),
   * Restore the verified final tree into it (`jj restore --from <verified-wip-tip>`),
   * Peel off one logical slice at a time using explicit file paths:
     ```bash
     jj commit -m "docs(spec): extend specification to Stage 2 Nonstandard Clifford Analysis" SPEC.md
     jj commit -m "tex(clifford-foundations): ..." tex/preamble.tex tex/main.tex ...
     ```
   * Abandon the old `wip` chain (`jj abandon <wip-commits>`) once the final commit tree matches byte-for-byte (`jj diff --from <verified-wip-tip> --to @-` is empty!).

---

## 8. Step-by-Step Manual Reconstruction Exercises

To internalize both mathematical frameworks by coding manually, try these four self-contained exercises in a scratch branch (`jj new main`):

1. **Prove 3D Cross-Product Duality in `NNScaling/Clifford.lean`:**
   In $\mathcal{C}\ell_3(\mathbb{R})$ (`euclideanQuadForm ℝ 3`), define the unit pseudoscalar $I_3 := e_0 e_1 e_2$. Prove that $I_3^2 = -1$ (`I3 * I3 = -1`) just like `unit_bivector_sq_neg_one`, and verify that $-(u \wedge v) I_3$ recovers the classical 3D cross product $u \times v$!
2. **Formalize Rotor Composition (`Spin(2)` Angle Addition):**
   Using `planarRotor Q e₁ e₂`, prove that multiplying two planar rotors `planarRotor Q e₁ e₂ c₁ s₁ * planarRotor Q e₁ e₂ c₂ s₂` equals `planarRotor Q e₁ e₂ (c₁ * c₂ - s₁ * s₂) (c₁ * s₂ + s₁ * c₂)` whenever `Q e₁ = 1`, `Q e₂ = 1`, `Q.IsOrtho e₁ e₂`.
3. **Verify Infinitesimal Rotor Shadow via `stCliffordHom`:**
   Construct an explicit hyperreal planar rotor in `CliffordAlgebra (euclideanQuadForm LimitedSubring 2)` with $c = 1$ and infinitesimal angle $s \in \mathbb{I}$, apply `stCliffordHom 2`, and prove its standard-part multivector shadow equals `1`!
4. **Derive the ReLU Correlation Fixed Point in `NNScaling/Ch02_Kernels.lean`:**
   Formalize Cho–Saul's correlation map $c(\rho) = \frac{\sqrt{1-\rho^2} + (\pi - \arccos\rho)\rho}{\pi}$ and prove $c(1) = 1$, $c(0) = 1/\pi$, and $c(-1) = 0$.
