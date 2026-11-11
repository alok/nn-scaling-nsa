import NNScaling.Foundations
import NNScaling.Ch01_Introduction
import NNScaling.Ch02_Kernels
import NNScaling.Ch03_DoubleDescent
import NNScaling.Ch04_FeatureLearning
import NNScaling.Ch05_DepthSDE
import NNScaling.Ch06_ProportionalTopics
import NNScaling.AppendixA_Technical

/-!
# Lecture Notes on Neural Network Scaling Limits (Nonstandard Analysis Edition)

This site is a literate Lean 4 / Verso companion and formalization for our **Nonstandard Analysis**
edition of Mufan Li's _Lecture Notes on Neural Network Scaling Limits_ (STAT 946, University of Waterloo).

* **Compiled Monograph PDF (Pure Nonstandard Analysis Edition):** [nn\_scaling\_nsa.pdf](pdf/nn_scaling_nsa.pdf)
* **Source Repository:** [github.com/alok/nn-scaling-nsa](https://github.com/alok/nn-scaling-nsa)

## Mathematical Framework

Every asymptotic scaling limit in Mufan Li's 98-page lecture notes is reformulated at an unlimited
hyperfinite network scale $`N, D, M \in {}^*\mathbb{N} \setminus \mathbb{N}` inside Robinson's enlargement
$`({}^*\mathbb{R}, {}^*\mathbb{N})`, paired with Mathlib's hyperreal field {name}`Hyperreal` ($`\mathbb{R}^*`)
and Loeb probability spaces $`(\Omega, \mathcal{L}(\mathcal{A}), L({}^*\mathbb{P}))`:

* Asymptotic rates $`O(N^{-\alpha})` and $`\Theta(1)` become exact algebraic membership in the ring of
  **limited hyperreals** $`\mathbb{L}`, the maximal ideal of **infinitesimals** $`\mathbb{I}` ($`\approx`),
  and the multiplicative group of **appreciable hyperreals** $`\mathbb{A} = \mathbb{L} \setminus \mathbb{I}` ($`\asymp`).
* Distributional, weak-measure, and Skorohod diffusion limits become **standard-part shadows** via the
  ring homomorphism $`\operatorname{st} : \mathbb{L} \to \mathbb{R}`, Anderson's hyperfinite Brownian motion,
  and Keisler–Lindstrøm hyperfinite stochastic difference equations.
* Mufan Li's prose, narrative structure, theorem numbering, figures, tables, and exercises are preserved
  in the full LaTeX monograph while every proof and algebraic spine is formalized cleanly below.

## Contents

0. [Nonstandard Analysis & Loeb Probability Foundations](NNScaling/Foundations/)
1. [Introduction: Scaling Laws as Infinitesimal Microscopes](NNScaling/Ch01_Introduction/)
2. [Kernel Limits for Wide Networks: NNGP and NTK](NNScaling/Ch02_Kernels/)
3. [Double Descent with Random Projections](NNScaling/Ch03_DoubleDescent/)
4. [Feature Learning and Mean-Field Limits](NNScaling/Ch04_FeatureLearning/)
5. [Depth Scaling and Covariance SDE Limits](NNScaling/Ch05_DepthSDE/)
6. [Further Topics in Proportional Depth-Width Scaling](NNScaling/Ch06_ProportionalTopics/)
7. [Appendix A: Technical Complements](NNScaling/AppendixA_Technical/)

## Verification Guarantees

All declarations in {lit}`NNScaling` compile on Lean {lit}`v4.35.0` + Mathlib {lit}`v4.35.0` with
{lit}`autoImplicit = false`, **zero** custom axioms, and **zero** {lit}`sorry` placeholders across the
formalized algebraic, hyperreal, differential, and projection theorems. See {lit}`COVERAGE.md` in the
repository for the complete chapter-by-chapter mapping between the LaTeX monograph and Lean modules.
-/
