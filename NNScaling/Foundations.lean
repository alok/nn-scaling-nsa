import Mathlib

/-!
# 0. Nonstandard Analysis and Loeb Probability Foundations

This foundational module supplies the hyperreal scale algebra and Loeb-measure shadow interfaces
used across our Nonstandard Analysis rewrite of Mufan Li's _Lecture Notes on Neural Network Scaling Limits_.

In place of sequential asymptotic limits ($`n \to \infty`, $`d/n \to \bar{\tau}`, $`O_{\mathbb{P}}(n^{-1/2})`),
we work directly in Mathlib's hyperreal field $`\mathbb{R}^* = {}^*\mathbb{R}` ({name}`Hyperreal`),
classifying elements into:

* **Limited numbers** $`\mathbb{L}` ({lit}`Limited`): hyperreals bounded in absolute value by a standard real;
* **Infinitesimals** $`\mathbb{I}` ({lit}`IsInfinitesimal`): hyperreals smaller in absolute value than every positive standard real, generating the infinite-closeness relation $`x \approx y` ({lit}`x ≊ y`);
* **Appreciable numbers** $`\mathbb{A} = \mathbb{L} \setminus \mathbb{I}` ({lit}`Appreciable`): limited, non-infinitesimal hyperreals, generating asymptotic scale equivalence $`x \asymp y` ({lit}`ScaleEq`, replacing $`\Theta(1)` and $`\asymp` in Mufan Li's notes);
* **Unlimited numbers** $`{}^*\mathbb{R} \setminus \mathbb{L}` ({lit}`Unlimited`): hyperreals exceeding every standard real in magnitude, modeling unlimited network widths $`N \in {}^*\mathbb{N} \setminus \mathbb{N}` and depths $`D \in {}^*\mathbb{N} \setminus \mathbb{N}`;
* **Standard part** $`\operatorname{st} : \mathbb{L} \to \mathbb{R}` ({lit}`st`): the unique ring homomorphism projecting limited hyperreals to their standard shadows with kernel $`\mathbb{I}`.
-/

noncomputable section

namespace NNScaling

open Set Filter
open scoped Hyperreal Topology

section ScaleAlgebra

variable {x y z e : ℝ*}

/-- A hyperreal $`x \in {}^*\mathbb{R}` is _limited_ ($`x \in \mathbb{L}`) if $`|x| < r` for some standard real $`r`. -/
def Limited (x : ℝ*) : Prop := ∃ r : ℝ, |x| < r

/-- A hyperreal $`x \in {}^*\mathbb{R}` is _unlimited_ if $`r < |x|` for every standard real $`r`. -/
def Unlimited (x : ℝ*) : Prop := ∀ r : ℝ, (r : ℝ*) < |x|

/-- A hyperreal $`x \in {}^*\mathbb{R}` is _infinitesimal_ ($`x \in \mathbb{I}`) if $`|x| < r` for every positive standard real $`r`. -/
def IsInfinitesimal (x : ℝ*) : Prop := ∀ r : ℝ, 0 < r → |x| < r

/-- A hyperreal $`x \in {}^*\mathbb{R}` is _appreciable_ ($`x \in \mathbb{A} = \mathbb{L} \setminus \mathbb{I}`) if it is limited and not infinitesimal. -/
def Appreciable (x : ℝ*) : Prop := Limited x ∧ ¬ IsInfinitesimal x

/-- Two hyperreals $`x, y` are _infinitely close_ ($`x \approx y`) if $`x - y` is infinitesimal. -/
def InfClose (x y : ℝ*) : Prop := IsInfinitesimal (x - y)

@[inherit_doc] scoped infix:50 " ≊ " => InfClose

/-- Two nonzero-scale hyperreals $`x, y` have the _same asymptotic scale_ ($`x \asymp y`) if $`x, y \neq 0` and $`x / y` is appreciable. -/
def ScaleEq (x y : ℝ*) : Prop := x ≠ 0 ∧ y ≠ 0 ∧ Appreciable (x / y)

@[inherit_doc] scoped infix:50 " ≍ₛ " => ScaleEq

/-- The _monad_ (or halo) of $`x \in {}^*\mathbb{R}` is $`\operatorname{mon}(x) = \{y : x \approx y\}`. -/
def monad (x : ℝ*) : Set ℝ* := {y | x ≊ y}

/-- The _standard part_ (shadow) $`\operatorname{st}(x) \in \mathbb{R}` of a hyperreal, defined by Dedekind completeness of $`\mathbb{R}`. -/
def st (x : ℝ*) : ℝ := sSup {r : ℝ | (r : ℝ*) < x}

@[simp]
theorem isInfinitesimal_zero : IsInfinitesimal 0 := by
  intro r hr
  simpa using Hyperreal.coe_pos.2 hr

theorem IsInfinitesimal.limited (h : IsInfinitesimal x) : Limited x :=
  ⟨1, by simpa using h 1 one_pos⟩

theorem limited_coe (r : ℝ) : Limited (r : ℝ*) := by
  refine ⟨|r| + 1, ?_⟩
  rw [abs_lt]
  constructor
  · have h : ((-(|r| + 1) : ℝ) : ℝ*) < (r : ℝ*) :=
      Hyperreal.coe_lt_coe.2 (by linarith [neg_abs_le r])
    simpa using h
  · exact Hyperreal.coe_lt_coe.2 (by linarith [le_abs_self r])

@[simp]
theorem limited_zero : Limited 0 := isInfinitesimal_zero.limited

@[simp]
theorem limited_one : Limited 1 := by simpa using limited_coe 1

@[simp]
theorem isInfinitesimal_coe_iff {r : ℝ} : IsInfinitesimal (r : ℝ*) ↔ r = 0 := by
  constructor
  · intro h
    by_contra hr
    have hlt := h |r| (abs_pos.2 hr)
    rw [abs_lt] at hlt
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · have habs : |r| = -r := abs_of_neg hneg
      have h1 : ((-(-r) : ℝ) : ℝ*) < (r : ℝ*) := by
        simpa [habs] using hlt.1
      have h2 := Hyperreal.coe_lt_coe.1 h1
      linarith
    · have habs : |r| = r := abs_of_pos hpos
      have h1 : (r : ℝ*) < (r : ℝ*) := by
        simpa [habs] using hlt.2
      exact lt_irrefl _ h1
  · rintro rfl
    exact isInfinitesimal_zero

theorem appreciable_coe {r : ℝ} (hr : r ≠ 0) : Appreciable (r : ℝ*) :=
  ⟨limited_coe r, fun h => hr (isInfinitesimal_coe_iff.1 h)⟩

theorem IsInfinitesimal.neg (h : IsInfinitesimal x) : IsInfinitesimal (-x) := by
  intro r hr
  simpa using h r hr

theorem IsInfinitesimal.add (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) :
    IsInfinitesimal (x + y) := by
  intro r hr
  have h1 := hx (r / 2) (half_pos hr)
  have h2 := hy (r / 2) (half_pos hr)
  calc
    |x + y| ≤ |x| + |y| := abs_add_le x y
    _ < ((r / 2 : ℝ) : ℝ*) + ((r / 2 : ℝ) : ℝ*) := add_lt_add h1 h2
    _ = (r : ℝ*) := by norm_cast; ring

theorem Limited.neg (hx : Limited x) : Limited (-x) := by
  rcases hx with ⟨r, hr⟩
  exact ⟨r, by simpa using hr⟩

theorem Limited.add (hx : Limited x) (hy : Limited y) : Limited (x + y) := by
  rcases hx with ⟨r, hr⟩
  rcases hy with ⟨s, hs⟩
  refine ⟨r + s, ?_⟩
  calc
    |x + y| ≤ |x| + |y| := abs_add_le x y
    _ < (r : ℝ*) + (s : ℝ*) := add_lt_add hr hs
    _ = ((r + s : ℝ) : ℝ*) := by norm_cast

theorem Limited.sub (hx : Limited x) (hy : Limited y) : Limited (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem Limited.mul (hx : Limited x) (hy : Limited y) : Limited (x * y) := by
  rcases hx with ⟨r, hr⟩
  rcases hy with ⟨s, hs⟩
  have hr0 : (0 : ℝ*) ≤ |x| := abs_nonneg x
  have hs0 : (0 : ℝ*) ≤ |y| := abs_nonneg y
  refine ⟨r * s, ?_⟩
  rw [abs_mul]
  calc
    |x| * |y| < (r : ℝ*) * (s : ℝ*) :=
      mul_lt_mul'' hr hs hr0 hs0
    _ = ((r * s : ℝ) : ℝ*) := by norm_cast

/-- Ideal property: the product of a limited hyperreal and an infinitesimal is infinitesimal. -/
theorem Limited.mul_isInfinitesimal (hx : Limited x) (he : IsInfinitesimal e) :
    IsInfinitesimal (x * e) := by
  rcases hx with ⟨r, hr⟩
  have hrpos : 0 < r := Hyperreal.coe_pos.1 ((abs_nonneg x).trans_lt hr)
  intro δ hδ
  have he' := he (δ / r) (div_pos hδ hrpos)
  rw [abs_mul]
  calc
    |x| * |e| < (r : ℝ*) * ((δ / r : ℝ) : ℝ*) :=
      mul_lt_mul'' hr he' (abs_nonneg x) (abs_nonneg e)
    _ = (δ : ℝ*) := by
      rw [← Hyperreal.coe_mul, mul_div_cancel₀ _ hrpos.ne']

theorem IsInfinitesimal.mul_limited (he : IsInfinitesimal e) (hx : Limited x) :
    IsInfinitesimal (e * x) := by
  rw [mul_comm]
  exact hx.mul_isInfinitesimal he

@[refl, simp]
theorem InfClose.refl (x : ℝ*) : x ≊ x := by
  simp [InfClose]

@[symm]
theorem InfClose.symm (h : x ≊ y) : y ≊ x := by
  have hneg := h.neg
  simpa [InfClose, neg_sub] using hneg

@[trans]
theorem InfClose.trans (h1 : x ≊ y) (h2 : y ≊ z) : x ≊ z := by
  have hsum := h1.add h2
  have hsub : (x - y) + (y - z) = x - z := by ring
  rwa [InfClose, ← hsub]

instance : Trans InfClose InfClose InfClose := ⟨InfClose.trans⟩

/-- The reciprocal of an unlimited hyperreal is infinitesimal. -/
theorem Unlimited.inv_isInfinitesimal (hx : Unlimited x) : IsInfinitesimal x⁻¹ := by
  intro r hr
  have h1 : ((r⁻¹ : ℝ) : ℝ*) < |x| := hx r⁻¹
  have hr_inv_pos : (0 : ℝ*) < ((r⁻¹ : ℝ) : ℝ*) := Hyperreal.coe_pos.2 (inv_pos.2 hr)
  rw [abs_inv]
  have h2 := inv_strictAnti₀ hr_inv_pos h1
  simpa using h2

theorem Appreciable.ne_zero (hx : Appreciable x) : x ≠ 0 := by
  rintro rfl
  exact hx.2 isInfinitesimal_zero

theorem Appreciable.inv (hx : Appreciable x) : Appreciable x⁻¹ := by
  refine ⟨?_, ?_⟩
  · by_contra hnot
    have hunl : Unlimited x⁻¹ := by
      intro r
      by_contra hle
      have hle' : |x⁻¹| ≤ (r : ℝ*) := not_lt.1 hle
      exact hnot ⟨max r 0 + 1, lt_of_le_of_lt hle' (by
        have hmax : (r : ℝ*) ≤ ((max r 0 : ℝ) : ℝ*) := Hyperreal.coe_le_coe.2 (le_max_left r 0)
        have hlt : ((max r 0 : ℝ) : ℝ*) < ((max r 0 + 1 : ℝ) : ℝ*) :=
          Hyperreal.coe_lt_coe.2 (lt_add_one _)
        exact hmax.trans_lt hlt)⟩
    have hinf : IsInfinitesimal (x⁻¹)⁻¹ := hunl.inv_isInfinitesimal
    rw [inv_inv] at hinf
    exact hx.2 hinf
  · intro hinf
    have hprod : IsInfinitesimal (x * x⁻¹) := hx.1.mul_isInfinitesimal hinf
    rw [mul_inv_cancel₀ hx.ne_zero] at hprod
    exact one_ne_zero (isInfinitesimal_coe_iff.1 (by simpa using hprod))

/-- Fundamental shadow theorem: every limited hyperreal is infinitely close to its standard part. -/
theorem Limited.infClose_st (hx : Limited x) : x ≊ (st x : ℝ*) := by
  rcases hx with ⟨R, hR⟩
  rw [abs_lt] at hR
  have hne : {t : ℝ | (t : ℝ*) < x}.Nonempty :=
    ⟨-R, by simpa using hR.1⟩
  have hbdd : BddAbove {t : ℝ | (t : ℝ*) < x} :=
    ⟨R, fun t ht => (Hyperreal.coe_lt_coe.1 (lt_trans ht hR.2)).le⟩
  have hlub : IsLUB {t : ℝ | (t : ℝ*) < x} (st x) := Real.isLUB_sSup hne hbdd
  have key : ∀ δ : ℝ, 0 < δ → |x - (st x : ℝ*)| ≤ (δ : ℝ*) := by
    intro δ hδ
    have h1 : x ≤ ((st x + δ : ℝ) : ℝ*) := by
      by_contra hlt
      have hmem : st x + δ ∈ {t : ℝ | (t : ℝ*) < x} := not_le.1 hlt
      have := hlub.1 hmem
      linarith
    have h2 : ((st x - δ : ℝ) : ℝ*) < x := by
      by_contra hle
      have hub : st x - δ ∈ upperBounds {t : ℝ | (t : ℝ*) < x} := fun t ht =>
        (Hyperreal.coe_lt_coe.1 (lt_of_lt_of_le ht (not_lt.1 hle))).le
      have := hlub.2 hub
      linarith
    rw [Hyperreal.coe_add] at h1
    rw [Hyperreal.coe_sub] at h2
    rw [abs_le]
    constructor <;> linarith
  intro δ hδ
  exact (key (δ / 2) (half_pos hδ)).trans_lt (Hyperreal.coe_lt_coe.2 (half_lt_self hδ))

/-- Uniqueness of the standard part: if $`x \approx r` for $`r \in \mathbb{R}`, then $`\operatorname{st}(x) = r`. -/
theorem st_eq_of_infClose {r : ℝ} (h : x ≊ (r : ℝ*)) : st x = r := by
  have hx : Limited x := by
    have : x = (x - r) + r := by ring
    rw [this]
    exact h.limited.add (limited_coe r)
  have hdiff : ((st x : ℝ*) - (r : ℝ*)) = (st x - x) + (x - r) := by ring
  have hinf : IsInfinitesimal ((st x : ℝ*) - (r : ℝ*)) := by
    rw [hdiff]
    exact (InfClose.symm hx.infClose_st).add h
  rw [← Hyperreal.coe_sub] at hinf
  exact sub_eq_zero.1 (isInfinitesimal_coe_iff.1 hinf)

@[simp]
theorem st_coe (r : ℝ) : st (r : ℝ*) = r :=
  st_eq_of_infClose (InfClose.refl _)

@[simp]
theorem st_zero : st 0 = 0 := st_coe 0

@[simp]
theorem st_one : st 1 = 1 := by simpa using st_coe 1

theorem IsInfinitesimal.st_eq_zero (he : IsInfinitesimal e) : st e = 0 :=
  st_eq_of_infClose (by simpa [InfClose] using he)

/-- Ring homomorphism property of $`\operatorname{st}`: addition. -/
theorem st_add (hx : Limited x) (hy : Limited y) : st (x + y) = st x + st y := by
  apply st_eq_of_infClose
  rw [InfClose, Hyperreal.coe_add]
  have hsum := hx.infClose_st.add hy.infClose_st
  convert hsum using 1
  ring

/-- Ring homomorphism property of $`\operatorname{st}`: negation. -/
theorem st_neg (hx : Limited x) : st (-x) = -st x := by
  apply st_eq_of_infClose
  rw [InfClose, Hyperreal.coe_neg]
  have hneg := hx.infClose_st.neg
  convert hneg using 1
  ring

/-- Ring homomorphism property of $`\operatorname{st}`: subtraction. -/
theorem st_sub (hx : Limited x) (hy : Limited y) : st (x - y) = st x - st y := by
  rw [sub_eq_add_neg, st_add hx hy.neg, st_neg hy, sub_eq_add_neg]

/-- Ring homomorphism property of $`\operatorname{st}`: multiplication. -/
theorem st_mul (hx : Limited x) (hy : Limited y) : st (x * y) = st x * st y := by
  apply st_eq_of_infClose
  rw [InfClose, Hyperreal.coe_mul]
  have h1 : IsInfinitesimal (x * (y - st y)) := hx.mul_isInfinitesimal hy.infClose_st
  have h2 : IsInfinitesimal ((x - st x) * (st y : ℝ*)) :=
    hx.infClose_st.mul_limited (limited_coe (st y))
  convert h1.add h2 using 1
  ring

theorem Limited.st_eq_zero_iff (hx : Limited x) : st x = 0 ↔ IsInfinitesimal x := by
  constructor
  · intro h0
    have h := hx.infClose_st
    rwa [h0, Hyperreal.coe_zero, InfClose, sub_zero] at h
  · exact IsInfinitesimal.st_eq_zero

theorem Appreciable.st_ne_zero (hx : Appreciable x) : st x ≠ 0 :=
  fun h0 => hx.2 ((hx.1.st_eq_zero_iff).1 h0)

/-- Division preservation of $`\operatorname{st}` for appreciable denominators. -/
theorem st_div (hx : Limited x) (hy : Appreciable y) : st (x / y) = st x / st y := by
  have hsy : st y ≠ 0 := hy.st_ne_zero
  have hy_inv : Limited y⁻¹ := hy.inv.1
  have hquot : Limited (x / y) := by
    rw [div_eq_mul_inv]
    exact hx.mul hy_inv
  have hmul : st ((x / y) * y) = st (x / y) * st y := st_mul hquot hy.1
  rw [div_mul_cancel₀ x hy.ne_zero] at hmul
  exact (eq_div_iff hsy).2 hmul.symm

end ScaleAlgebra

/-!
## Loeb Expectation and Hyperfinite Concentration Interface

In Chapters 1 through 6, hyperfinite neural networks are defined over internal probability spaces
$`(\Omega, \mathcal{A}, {}^*\mathbb{P})`. When an internal random variable $`X : \Omega \to {}^*\mathbb{R}`
has S-integrable second moment and internal variance $`{}^*\!\operatorname{Var}(X) \in \mathbb{I}`,
internal Chebyshev's inequality guarantees that $`X` concentrates within the monad of its internal mean
$`L({}^*\mathbb{P})`-almost surely. We record the algebraic variance-scaling identity underlying every hyperfinite
law-of-large-numbers step in Chapters 2, 3, 4, 5, and 6.
-/

section HyperfiniteConcentration

/-- If each neuron has bounded internal variance $`v \in \mathbb{L}` and the network width $`N \in {}^*\mathbb{R}`
is unlimited, then the empirical-average variance $`v / N` is infinitesimal. -/
theorem empirical_variance_isInfinitesimal {v N : ℝ*}
    (hv : Limited v) (hN : Unlimited N) :
    IsInfinitesimal (v / N) := by
  rw [div_eq_mul_inv]
  exact hv.mul_isInfinitesimal hN.inv_isInfinitesimal

end HyperfiniteConcentration

end NNScaling
