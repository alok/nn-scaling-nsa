import NNScaling.Foundations
import NNScaling.Clifford
import NNScaling.Ch01_Introduction
import NNScaling.Ch02_Kernels
import NNScaling.Ch03_DoubleDescent
import NNScaling.Ch04_FeatureLearning
import NNScaling.Ch05_DepthSDE
import NNScaling.Ch06_ProportionalTopics
import NNScaling.AppendixA_Technical

/-!
# Lecture Notes on Neural Network Scaling Limits (Nonstandard Clifford Analysis Edition)

This site is a literate Lean 4 / Verso companion and formalization for our two-stage rewrite of
Mufan Li's _Lecture Notes on Neural Network Scaling Limits_ (STAT 946, University of Waterloo),
progressing from **Stage 1: Pure Nonstandard Analysis** (bookmark {lit}`nsa`) to **Stage 2:
Nonstandard Clifford Analysis** (bookmark {lit}`main`).

* **Stage 2 Monograph PDF (Nonstandard Clifford Analysis Edition):** [nn\_scaling\_clifford.pdf](pdf/nn_scaling_clifford.pdf)
* **Stage 1 Monograph PDF (Pure Nonstandard Analysis Edition):** [nn\_scaling\_nsa.pdf](pdf/nn_scaling_nsa.pdf)
* **Source Repository:** [github.com/alok/nn-scaling-nsa](https://github.com/alok/nn-scaling-nsa)

## Mathematical Framework

Every asymptotic scaling limit in Mufan Li's 98-page lecture notes is reformulated at an unlimited
hyperfinite network scale $`N, D, M \in {}^*\mathbb{N} \setminus \mathbb{N}` inside Robinson's enlargement
$`({}^*\mathbb{R}, {}^*\mathbb{N})`, paired with Mathlib's {name}`Hyperreal` ($`\mathbb{R}^*`), Loeb
probability spaces $`(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))`, and Mathlib's
{name}`CliffordAlgebra` over standard ($`\mathbb{R}`), limited ($`\mathbb{L}`), and hyperreal
($`\mathbb{R}^*`) rings:

* **Hyperreal Valuation Ring & Standard-Part Homomorphisms:** Asymptotic rates $`O(N^{-\alpha})` and
  $`\Theta(1)` become exact algebraic membership in the subring of **limited hyperreals**
  $`\mathbb{L}` ({lit}`LimitedSubring`), the maximal ideal of **infinitesimals** $`\mathbb{I}`
  ({lit}`InfinitesimalIdeal`), and **appreciable hyperreals** $`\mathbb{A} = \mathbb{L} \setminus \mathbb{I}`.
  Lifting $`\operatorname{st} : \mathbb{L} \to \mathbb{R}` ({lit}`stRingHom`) via {name}`CliffordAlgebra.lift`
  yields the multivector shadow homomorphism {lit}`stCliffordHom`
  ($`\operatorname{st}_{\mathcal{C}\ell} : \mathcal{C}\ell_n(\mathbb{L}) \to \mathcal{C}\ell_n(\mathbb{R})`).
* **Geometric Product, Rotors, Blades, & Dirac Operators:** Empirical NNGP/NTK Gram matrices become
  scalar-grade geometric products $`\frac{1}{N}\langle u v^{\sim}\rangle_0`; Cho–Saul ReLU kernels,
  $`\mathcal{C}\ell_2^+` Cauchy–Dirac Stieltjes kernels, and $`\operatorname{Spin}(m)` Dyson eigenvalue
  repulsion emerge from unit bivectors $`\hat{B}^2 = -1`; Gaussian conditioning and double-descent
  Schur complements become coordinate-free Hestenes blade contractions and wedge-volume ratios; and
  mean-field continuity PDEs take the monogenic Dirac form $`\partial_t \rho_t + \langle \partial_\theta (v_t \rho_t)\rangle_0 = 0`.
* **Prose & Structure Preservation:** Mufan Li's prose, narrative transitions, theorem numbering,
  figures, tables, and exercises are preserved faithfully across both full LaTeX monographs.

## Contents

0. [0A. Nonstandard Analysis & Loeb Probability Foundations](NNScaling/Foundations/)
1. [0B. Nonstandard Clifford Analysis Foundations](NNScaling/Clifford/)
2. [1. Introduction: Scaling Laws, Cauchy–Dirac Resolvents, & Dirac Transport](NNScaling/Ch01_Introduction/)
3. [2. Kernel Limits for Wide Networks: Rotor NNGP & Dirac NTK](NNScaling/Ch02_Kernels/)
4. [3. Double Descent via Wedge-Blade Volumes & Hestenes Projections](NNScaling/Ch03_DoubleDescent/)
5. [4. Feature Learning, $`\mu`P, & Monogenic Dirac Transport](NNScaling/Ch04_FeatureLearning/)
6. [5. Depth Scaling & Hyperreal Clifford Covariance SDEs](NNScaling/Ch05_DepthSDE/)
7. [6. Shaped Attention Multivectors & $`\operatorname{Spin}(m)` Dyson Brownian Motion](NNScaling/Ch06_ProportionalTopics/)
8. [Appendix A: Technical Complements & Blade Conditioning](NNScaling/AppendixA_Technical/)

## Verification Guarantees

All declarations in {lit}`NNScaling` compile on Lean {lit}`v4.35.0` + Mathlib {lit}`v4.35.0` with
{lit}`autoImplicit = false`, **zero** custom axioms, and **zero** {lit}`sorry` placeholders across
all hyperreal, Clifford, differential, and projection theorems. See {lit}`COVERAGE.md` and
{lit}`DEVELOPER_GUIDE.md` in the repository for the complete theorem-by-theorem mapping and
from-scratch engineering guide.
-/
