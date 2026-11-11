import NNScaling.Foundations

/-!
# 4. Feature Learning and Mean-Field Limits

Chapters 2 and 3 studied lazy/fixed-feature regimes in which representations move infinitesimally
($`\frac{1}{N}\|\Delta h^\alpha\|^2 \in \mathbb{I}`). Chapter 4 studies _feature learning_, characterized in
nonstandard analysis by requiring the normalized squared pre-activation update to lie in the
appreciable group $`\mathbb{A} = \mathbb{L} \setminus \mathbb{I}` (**Definitions 4.1 and 4.6**):
$$`\frac{1}{N}\left\lVert \Delta_{W_{\ell-1}} h_\ell(x^\alpha)\right\rVert^2 \in \mathbb{A}.`

## 4.1 & 4.4 Scaling Balance and Maximal Update ($`\mu`P)

Writing $`\gamma_N \asymp N^p` and $`\eta_N \asymp N^q` at unlimited width $`N \in {}^*\mathbb{N} \setminus \mathbb{N}`,
**Steps 1–6** of Section 4.4 and **Exercise 4.7.1** show that:

* Feature updates scale with exponent $`q - p - 1/2`;
* Output updates scale with exponent $`q - 2p`.

Requiring both updates to be appreciable ($`\in \mathbb{A}`, i.e. scale exponent $`0`) uniquely selects
$`(p, q) = (1/2, 1)`, corresponding to $`\gamma_N \asymp \sqrt{N}` (overall output prefactor $`1/N`)
and $`\eta_N \asymp N`.
-/

noncomputable section

namespace NNScaling.Ch04

open NNScaling BigOperators Finset
open scoped Hyperreal NNScaling

/-- **Equation (4.66):** Feature-update width exponent $`q - p - 1/2` when $`\gamma_N \asymp N^p, \eta_N \asymp N^q`. -/
def featureUpdateExp (p q : ℝ) : ℝ := q - p - 1 / 2

/-- **Equation (4.66):** Predictor-speed width exponent $`q - 2p` when $`\gamma_N \asymp N^p, \eta_N \asymp N^q`. -/
def predictorSpeedExp (p q : ℝ) : ℝ := q - 2 * p

/-- **Exercise 4.7.1 & Equation (4.53) (Uniqueness of Maximal-Update / Mean-Field Exponents).**
Both feature updates and predictor speed have appreciable ($`N^0`) scale if and only if
$`(p, q) = (1/2, 1)`, i.e. $`\gamma_N \asymp \sqrt{N}` and $`\eta_N \asymp N`. -/
theorem mup_exponent_balance_iff (p q : ℝ) :
    (featureUpdateExp p q = 0 ∧ predictorSpeedExp p q = 0) ↔ (p = 1 / 2 ∧ q = 1) := by
  unfold featureUpdateExp predictorSpeedExp
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- **Exercise 4.7.1 (Lazy NTK Exponents).** At $`(p, q) = (0, 0)`, predictor speed is $`N^0` (appreciable)
while per-coordinate feature updates have exponent $`-1/2` (infinitesimal of scale $`N^{-1/2}`). -/
theorem ntk_lazy_exponents :
    featureUpdateExp 0 0 = -1 / 2 ∧ predictorSpeedExp 0 0 = 0 := by
  unfold featureUpdateExp predictorSpeedExp
  norm_num

/-- **Exercise 4.7.1 (Naive Large-Learning-Rate Exponents).** At $`(p, q) = (0, 1/2)`, feature updates
have exponent $`0` (appreciable), while predictor speed explodes with exponent $`+1/2` ($`N^{1/2}` unlimited). -/
theorem naive_large_lr_exponents :
    featureUpdateExp 0 (1 / 2) = 0 ∧ predictorSpeedExp 0 (1 / 2) = 1 / 2 := by
  unfold featureUpdateExp predictorSpeedExp
  norm_num

/-- **Hyperreal Scale Balance Theorem (Equations (4.47), (4.52), (4.53)).**
For positive hyperreals $`\eta, \gamma_N, \text{rtN}` with $`\text{rtN}^2 = N`, if $`\eta / (\gamma_N \cdot \text{rtN}) \in \mathbb{A}`
and $`\eta / \gamma_N^2 \in \mathbb{A}`, then $`\gamma_N / \text{rtN} \in \mathbb{A}` ($`\gamma_N \asymp \sqrt{N}`) and
$`\eta / N \in \mathbb{A}` ($`\eta \asymp N`). -/
theorem hyperreal_mup_scale_solution {η γN rtN N : ℝ*}
    (hη : η ≠ 0) (hγ : γN ≠ 0) (hrt : rtN ≠ 0) (hN_sq : rtN ^ 2 = N)
    (h_feat : Appreciable (η / (γN * rtN)))
    (h_pred : Appreciable (η / (γN ^ 2))) :
    Appreciable (γN / rtN) ∧ Appreciable (η / N) := by
  have h_inv_pred : Appreciable ((η / (γN ^ 2))⁻¹) := h_pred.inv
  have hγ_ratio_eq : γN / rtN = (η / (γN * rtN)) * (η / (γN ^ 2))⁻¹ := by
    field_simp [hη, hγ, hrt]
  have hγ_lim : Limited (γN / rtN) := by
    rw [hγ_ratio_eq]
    exact h_feat.1.mul h_inv_pred.1
  have hγ_app : Appreciable (γN / rtN) := by
    refine ⟨hγ_lim, fun hinf => ?_⟩
    have hst0 := hinf.st_eq_zero
    rw [hγ_ratio_eq, st_mul h_feat.1 h_inv_pred.1] at hst0
    exact mul_ne_zero h_feat.st_ne_zero h_inv_pred.st_ne_zero hst0
  have hη_ratio_eq : η / N = (η / (γN * rtN)) * (γN / rtN) := by
    rw [← hN_sq]
    field_simp [hγ, hrt]
  have hη_lim : Limited (η / N) := by
    rw [hη_ratio_eq]
    exact h_feat.1.mul hγ_app.1
  have hη_app : Appreciable (η / N) := by
    refine ⟨hη_lim, fun hinf => ?_⟩
    have hst0 := hinf.st_eq_zero
    rw [hη_ratio_eq, st_mul h_feat.1 hγ_app.1] at hst0
    exact mul_ne_zero h_feat.st_ne_zero hγ_app.st_ne_zero hst0
  exact ⟨hγ_app, hη_app⟩

/-- **Remark 4.7 & Exercise 4.7.2 (Shallow Mean Field as the $`d = 1` Maximal-Update NTK).**
When $`d = 1`, $`G_2^{\alpha\beta} = 1`, and $`g_{1,i}^\alpha = a_i \varphi'(h_i^\alpha)`, the two-term
normalized NTK sum $`G_1 \Phi_0 + G_2 \Phi_1` equals the shallow normalized NTK formula (4.12). -/
theorem shallow_normalized_ntk_eq_d1 {N : ℕ} (a φhα φhβ dφhα dφhβ : Fin N → ℝ) (Φ0αβ : ℝ) :
    let Φ1αβ := (1 / (N : ℝ)) * ∑ i : Fin N, φhα i * φhβ i
    let G1αβ := (1 / (N : ℝ)) * ∑ i : Fin N, (a i * dφhα i) * (a i * dφhβ i)
    let G2αβ := (1 : ℝ)
    G1αβ * Φ0αβ + G2αβ * Φ1αβ =
      (1 / (N : ℝ)) * (∑ i : Fin N, φhα i * φhβ i) +
        Φ0αβ * ((1 / (N : ℝ)) * ∑ i : Fin N, (a i) ^ 2 * dφhα i * dφhβ i) := by
  intro Φ1αβ G1αβ G2αβ
  dsimp [Φ1αβ, G1αβ, G2αβ]
  have hsum :
      (∑ i : Fin N, (a i * dφhα i) * (a i * dφhβ i)) =
        ∑ i : Fin N, (a i) ^ 2 * dφhα i * dφhβ i :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

/-- **Exercise 4.7.3 (DMFT Physical-to-Macroscopic Time Rescaling, Equations (4.65) and (4.67)).**
If physical time $`u` and macroscopic time $`t` are related by $`t(u) = c u` with $`c = \eta_N / (m \gamma_N^2)`,
then chain-rule differentiation converts $`\frac{d}{du} r^\alpha = -c \sum_\beta K^{\alpha\beta} r^\beta` into
the width-free macroscopic equation $`\frac{d}{dt} r^\alpha = -\sum_\beta K^{\alpha\beta} r^\beta`. -/
theorem dmft_time_rescaling {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    (r : Fin m → ℝ → ℝ) (K : ℝ → Fin m → Fin m → ℝ) (t : ℝ) (α : Fin m)
    (h_phys : HasDerivAt (fun u => r α (c * u)) (-c * ∑ β : Fin m, K (c * (t / c)) α β * r β (c * (t / c))) (t / c))
    (h_diff : DifferentiableAt ℝ (r α) t) :
    deriv (r α) t = -∑ β : Fin m, K t α β * r β t := by
  have hct : c * (t / c) = t := mul_div_cancel₀ t hc
  rw [hct] at h_phys
  have h_comp : HasDerivAt (fun u => r α (c * u)) (deriv (r α) t * c) (t / c) := by
    have h_inner : HasDerivAt (fun u : ℝ => c * u) c (t / c) := by
      simpa using (hasDerivAt_id (t / c)).const_mul c
    have h_outer : HasDerivAt (r α) (deriv (r α) t) (c * (t / c)) := by
      rw [hct]
      exact h_diff.hasDerivAt
    exact h_outer.comp (t / c) h_inner
  have heq : deriv (r α) t * c = -c * ∑ β : Fin m, K t α β * r β t :=
    h_comp.unique h_phys
  apply mul_right_cancel₀ hc
  linarith

end NNScaling.Ch04
