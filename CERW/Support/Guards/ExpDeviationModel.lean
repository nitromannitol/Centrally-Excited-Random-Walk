import CERW.Model
import CERW.Support.Lower.ExpDeviationAE
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Fair-coin martingales on interleaved sites

A model for `lem:exp-deviation`. The coins `Z₀, Z₁, …` are independent and take the values `±1`; they
are the coordinates of a sequence in `ℝ` under the product of the measure `½ δ₁ + ½ δ₋₁`, so a
coordinate has the value `±1` almost surely, not at every point. Site `i < m` follows the coin
`Z_{t+1}` at the times `t ≡ i (mod m)`. The process
`site b m i t = (Z₀² - 1) + b ∑_{k<t} 1{k ≡ i} Z_{k+1}` is a martingale for the natural filtration of
the coins; it starts at `0` and has increments of size at most `b` only almost surely. The
predictable bracket of site `i` at time `m L` is `L b²` and the brackets of two distinct sites are
`0`. The process `stopped b m n i` agrees with `site b m i` up to time `n` and jumps by `1`
afterwards, so it is a martingale up to time `n` only.
-/

namespace CERW.Support.Guards.CoinSites

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The fair coin with values `±1`, as a measure on `ℝ`. -/
def coinLaw : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure coinLaw :=
  ⟨by simp [coinLaw, ENNReal.inv_two_add_inv_two]⟩

/-- Independent fair coins, as a measure on sequences. -/
def law : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => coinLaw

instance : IsProbabilityMeasure law := by
  unfold law
  infer_instance

/-- The `k`-th coin. -/
def coin (k : ℕ) (ω : ℕ → ℝ) : ℝ := ω k

lemma measurable_coin (k : ℕ) : Measurable (coin k) := measurable_pi_apply k

lemma stronglyMeasurable_coin (k : ℕ) : StronglyMeasurable (coin k) :=
  (measurable_coin k).stronglyMeasurable

/-- The coins are independent. -/
lemma indep_coin : iIndepFun coin law :=
  iIndepFun_infinitePi (P := fun _ : ℕ => coinLaw) (X := fun _ => id) (fun _ => measurable_id)

lemma coinLaw_ae_sq : ∀ᵐ x ∂coinLaw, x ^ 2 = 1 := by
  refine ae_add_measure_iff.2 ⟨Measure.ae_smul_measure ?_ _, Measure.ae_smul_measure ?_ _⟩
  · rw [ae_dirac_eq, Filter.eventually_pure]
    norm_num
  · rw [ae_dirac_eq, Filter.eventually_pure]
    norm_num

/-- Every coin has square `1` almost surely. -/
lemma coin_sq_ae (k : ℕ) : ∀ᵐ ω ∂law, coin k ω ^ 2 = 1 :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => coinLaw) k).quasiMeasurePreserving.ae
    coinLaw_ae_sq

lemma abs_coin_le_one_ae (k : ℕ) : ∀ᵐ ω ∂law, |coin k ω| ≤ 1 :=
  (coin_sq_ae k).mono fun _ h => (sq_le_one_iff_abs_le_one _).1 h.le

lemma integral_coinLaw : ∫ x, x ∂coinLaw = 0 := by
  have hd : ∀ a : ℝ, Integrable (fun x : ℝ => x) (Measure.dirac a) :=
    fun a => integrable_dirac (by simp)
  unfold coinLaw
  rw [integral_add_measure ((hd 1).smul_measure (by simp)) ((hd (-1)).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp

/-- Every coin has mean `0`. -/
lemma integral_coin (k : ℕ) : ∫ ω, coin k ω ∂law = 0 := by
  have h := integral_map (μ := Measure.infinitePi (fun _ : ℕ => coinLaw))
    (φ := fun ω : ℕ → ℝ => ω k) (f := fun x : ℝ => x) (measurable_pi_apply k).aemeasurable
    aestronglyMeasurable_id
  rw [(measurePreserving_eval_infinitePi (fun _ : ℕ => coinLaw) k).map_eq, integral_coinLaw] at h
  exact h.symm

lemma integrable_coin (k : ℕ) : Integrable (coin k) law :=
  Integrable.of_bound (stronglyMeasurable_coin k).aestronglyMeasurable 1
    ((abs_coin_le_one_ae k).mono fun _ h => by rwa [Real.norm_eq_abs])

/-- The natural filtration of the coins. -/
def filt : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  Filtration.natural coin stronglyMeasurable_coin

/-- The coin `Z_{t+1}` has conditional mean `0` given the coins `Z₀, …, Z_t`. -/
lemma condExp_coin_succ (t : ℕ) : law[coin (t + 1) | filt t] =ᵐ[law] 0 := by
  have h : law[coin (t + 1) | filt t] =ᵐ[law] fun _ => ∫ ω, coin (t + 1) ω ∂law :=
    indep_coin.condExp_natural_ae_eq_of_lt stronglyMeasurable_coin (Nat.lt_succ_self t)
  filter_upwards [h] with ω hω
  rw [hω, integral_coin]
  rfl

/-- The increment of site `i` at time `t`: the coin `Z_{t+1}` if `t ≡ i (mod m)`, and `0`
otherwise. -/
def siteInc (m : ℕ) (i : Fin m) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  if t % m = (i : ℕ) then coin (t + 1) ω else 0

/-- Site `i`: the start `Z₀² - 1`, which vanishes almost surely but not at every point, plus `b`
times the sum of the increments. -/
def site (b : ℝ) (m : ℕ) (i : Fin m) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (coin 0 ω ^ 2 - 1) + b * ∑ k ∈ Finset.range t, siteInc m i k ω

lemma site_succ_sub (b : ℝ) (m : ℕ) (i : Fin m) (t : ℕ) (ω : ℕ → ℝ) :
    site b m i (t + 1) ω - site b m i t ω = b * siteInc m i t ω := by
  simp only [site, Finset.sum_range_succ]
  ring

lemma stronglyMeasurable_siteInc (m : ℕ) (i : Fin m) {s t : ℕ} (hst : s + 1 ≤ t) :
    StronglyMeasurable[filt t] (siteInc m i s) := by
  by_cases h : s % m = (i : ℕ)
  · have hfun : siteInc m i s = coin (s + 1) := funext fun ω => by simp [siteInc, h]
    rw [hfun]
    exact (Filtration.stronglyAdapted_natural stronglyMeasurable_coin (s + 1)).mono
      (filt.mono hst)
  · have hfun : siteInc m i s = fun _ => 0 := funext fun ω => by simp [siteInc, h]
    rw [hfun]
    exact stronglyMeasurable_const

lemma abs_siteInc_le_one_ae (m : ℕ) (i : Fin m) (t : ℕ) : ∀ᵐ ω ∂law, |siteInc m i t ω| ≤ 1 := by
  by_cases h : t % m = (i : ℕ)
  · filter_upwards [abs_coin_le_one_ae (t + 1)] with ω hω
    simpa [siteInc, h] using hω
  · filter_upwards with ω
    simp [siteInc, h]

lemma integrable_siteInc (m : ℕ) (i : Fin m) (t : ℕ) : Integrable (siteInc m i t) law :=
  Integrable.of_bound
    ((stronglyMeasurable_siteInc m i (le_refl (t + 1))).mono (filt.le (t + 1))).aestronglyMeasurable
    1 ((abs_siteInc_le_one_ae m i t).mono fun _ h => by rwa [Real.norm_eq_abs])

lemma stronglyAdapted_site (b : ℝ) (m : ℕ) (i : Fin m) : StronglyAdapted filt (site b m i) := by
  intro t
  have hZ : StronglyMeasurable[filt t] (coin 0) :=
    (Filtration.stronglyAdapted_natural stronglyMeasurable_coin 0).mono (filt.mono (Nat.zero_le t))
  have hsum : StronglyMeasurable[filt t] (fun ω => ∑ k ∈ Finset.range t, siteInc m i k ω) := by
    have hfun : StronglyMeasurable[filt t] (∑ k ∈ Finset.range t, fun ω => siteInc m i k ω) := by
      refine Finset.stronglyMeasurable_sum (f := fun k (ω : ℕ → ℝ) => siteInc m i k ω)
        (Finset.range t) ?_
      intro k hk
      exact stronglyMeasurable_siteInc m i (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    have heq : (∑ k ∈ Finset.range t, fun ω => siteInc m i k ω)
        = fun ω => ∑ k ∈ Finset.range t, siteInc m i k ω := by
      funext ω
      exact Finset.sum_apply ω (Finset.range t) fun k (ω : ℕ → ℝ) => siteInc m i k ω
    rwa [heq] at hfun
  exact (hZ.pow 2 |>.sub stronglyMeasurable_const).add (stronglyMeasurable_const.mul hsum)

lemma integrable_site (b : ℝ) (m : ℕ) (i : Fin m) (t : ℕ) : Integrable (site b m i t) law := by
  have h0 : Integrable (fun ω => coin 0 ω ^ 2 - 1) law :=
    (integrable_zero (ℕ → ℝ) ℝ law).congr ((coin_sq_ae 0).mono fun ω h => by simp [h])
  exact h0.add
    ((integrable_finsetSum (Finset.range t) fun k _ => integrable_siteInc m i k).const_mul b)

/-- Site `i` is a martingale for the natural filtration of the coins. -/
lemma martingale_site (b : ℝ) (m : ℕ) (i : Fin m) : Martingale (site b m i) filt law := by
  refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_site b m i)
    (integrable_site b m i) fun t => ?_
  by_cases h : t % m = (i : ℕ)
  · have hsub : site b m i (t + 1) - site b m i t = b • coin (t + 1) := by
      funext ω
      rw [Pi.sub_apply, site_succ_sub]
      simp [siteInc, h]
    rw [hsub]
    filter_upwards [condExp_smul b (coin (t + 1)) (filt t), condExp_coin_succ t] with ω h1 h2
    rw [h1, Pi.smul_apply, h2]
    simp
  · have hsub : site b m i (t + 1) - site b m i t = 0 := by
      funext ω
      rw [Pi.sub_apply, site_succ_sub]
      simp [siteInc, h]
    rw [hsub, condExp_zero]

/-- The start of every site is `0` almost surely. -/
lemma site_zero_ae (b : ℝ) (m : ℕ) (i : Fin m) : ∀ᵐ ω ∂law, site b m i 0 ω = 0 :=
  (coin_sq_ae 0).mono fun ω h => by simp [site, h]

/-- The increments of every site are at most `b` almost surely. -/
lemma site_inc_ae {b : ℝ} (hb : 0 < b) (m : ℕ) (i : Fin m) (t : ℕ) :
    ∀ᵐ ω ∂law, |site b m i (t + 1) ω - site b m i t ω| ≤ b :=
  (abs_siteInc_le_one_ae m i t).mono fun ω h => by
    rw [site_succ_sub, abs_mul, abs_of_pos hb]
    exact mul_le_of_le_one_right hb.le h

/-- Among the times `t < m L`, exactly `L` satisfy `t ≡ i (mod m)`. -/
lemma count_mod (m : ℕ) (i : Fin m) (L : ℕ) :
    ∑ t ∈ Finset.range (m * L), (if t % m = (i : ℕ) then (1 : ℝ) else 0) = L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h1 : ∀ x ∈ Finset.range m, (if (m * L + x) % m = (i : ℕ) then (1 : ℝ) else 0)
        = if x = (i : ℕ) then 1 else 0 := by
      intro x hx
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.range m) (i : ℕ) (fun _ => (1 : ℝ))]
    simp [i.isLt]

/-- The predictable bracket of a site at time `m L` is `L b²` almost surely. -/
lemma predBracket_site_same (b : ℝ) (m : ℕ) (i : Fin m) (L : ℕ) :
    CERW.predBracket law filt (site b m i) (site b m i) (m * L)
      =ᵐ[law] fun _ => (L : ℝ) * b ^ 2 := by
  have hterm : ∀ t ∈ Finset.range (m * L),
      law[fun ω => (site b m i (t + 1) ω - site b m i t ω) *
          (site b m i (t + 1) ω - site b m i t ω) | filt t]
        =ᵐ[law] fun _ => b ^ 2 * (if t % m = (i : ℕ) then 1 else 0) := by
    intro t _
    have hc : (fun ω => (site b m i (t + 1) ω - site b m i t ω) *
          (site b m i (t + 1) ω - site b m i t ω))
        =ᵐ[law] fun _ => b ^ 2 * (if t % m = (i : ℕ) then 1 else 0) := by
      filter_upwards [coin_sq_ae (t + 1)] with ω h
      simp only [site_succ_sub, siteInc]
      by_cases ht : t % m = (i : ℕ)
      · simp only [if_pos ht]
        calc b * coin (t + 1) ω * (b * coin (t + 1) ω) = b ^ 2 * coin (t + 1) ω ^ 2 := by ring
          _ = b ^ 2 * 1 := by rw [h]
      · simp [ht]
    refine (condExp_congr_ae hc).trans ?_
    rw [condExp_const (filt.le t)]
  have hall := (Filter.eventually_all_finset (Finset.range (m * L))).2 hterm
  filter_upwards [hall] with ω hω
  have hsum : ∑ t ∈ Finset.range (m * L), law[fun ω => (site b m i (t + 1) ω - site b m i t ω) *
        (site b m i (t + 1) ω - site b m i t ω) | filt t] ω
      = ∑ t ∈ Finset.range (m * L), b ^ 2 * (if t % m = (i : ℕ) then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl hω
  simp only [CERW.predBracket, Finset.sum_apply]
  rw [hsum, ← Finset.mul_sum, count_mod]
  ring

/-- The brackets of two distinct sites vanish. -/
lemma predBracket_site_cross (b : ℝ) (m : ℕ) {i j : Fin m} (hij : i ≠ j) (n : ℕ) :
    CERW.predBracket law filt (site b m i) (site b m j) n = 0 := by
  unfold CERW.predBracket
  refine Finset.sum_eq_zero fun t _ => ?_
  have hz : (fun ω => (site b m i (t + 1) ω - site b m i t ω) *
      (site b m j (t + 1) ω - site b m j t ω)) = 0 := by
    funext ω
    rw [site_succ_sub, site_succ_sub]
    by_cases hi : t % m = (i : ℕ)
    · have hj : ¬ t % m = (j : ℕ) := fun hj => hij (Fin.ext (hi.symm.trans hj))
      simp [siteInc, hj]
    · simp [siteInc, hi]
  rw [hz, condExp_zero]

/-- Site `i` up to time `n`, continued after time `n` by a jump of `1`. -/
def stopped (b : ℝ) (m n : ℕ) (i : Fin m) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  if t ≤ n then site b m i t ω else site b m i n ω + 1

lemma stopped_eq {b : ℝ} {m n : ℕ} {i : Fin m} {t : ℕ} (ht : t ≤ n) :
    stopped b m n i t = site b m i t :=
  funext fun ω => by simp [stopped, ht]

/-- The continuation of a site by a jump is not a martingale. -/
lemma not_martingale_stopped (b : ℝ) (m n : ℕ) (i : Fin m) :
    ¬ Martingale (stopped b m n i) filt law := by
  intro h
  have h1 := h.condExp_ae_eq (Nat.le_succ n)
  have hfun : stopped b m n i (n + 1) = fun ω => site b m i n ω + 1 := by
    funext ω
    simp [stopped]
  have hmeas : StronglyMeasurable[filt n] (fun ω => site b m i n ω + 1) :=
    (stronglyAdapted_site b m i n).add stronglyMeasurable_const
  have hint : Integrable (fun ω => site b m i n ω + 1) law :=
    (integrable_site b m i n).add (integrable_const 1)
  rw [hfun, condExp_of_stronglyMeasurable (filt.le n) hmeas hint] at h1
  have h2 : ∀ᵐ ω ∂law, site b m i n ω + 1 = site b m i n ω :=
    h1.mono fun ω hω => hω.trans (by simp [stopped])
  have h3 : ∀ᵐ ω ∂law, False := h2.mono fun ω hω => by linarith
  obtain ⟨_, hω⟩ := h3.exists
  exact hω

lemma stronglyMeasurable_stopped {b : ℝ} {m n : ℕ} (i : Fin m) {t : ℕ} (ht : t ≤ n) :
    StronglyMeasurable[filt t] (stopped b m n i t) := by
  rw [stopped_eq ht]
  exact stronglyAdapted_site b m i t

lemma integrable_stopped {b : ℝ} {m n : ℕ} (i : Fin m) {t : ℕ} (ht : t ≤ n) :
    Integrable (stopped b m n i t) law := by
  rw [stopped_eq ht]
  exact integrable_site b m i t

/-- The continuation of a site is a martingale up to time `n`. -/
lemma condExp_stopped {b : ℝ} {m n : ℕ} (i : Fin m) {t : ℕ} (ht : t < n) :
    law[stopped b m n i (t + 1) | filt t] =ᵐ[law] stopped b m n i t := by
  rw [stopped_eq (Nat.succ_le_of_lt ht), stopped_eq ht.le]
  exact (martingale_site b m i).condExp_ae_eq (Nat.le_succ t)

lemma stopped_zero_ae (b : ℝ) (m n : ℕ) (i : Fin m) : ∀ᵐ ω ∂law, stopped b m n i 0 ω = 0 := by
  rw [stopped_eq (Nat.zero_le n)]
  exact site_zero_ae b m i

lemma stopped_inc_ae {b : ℝ} (hb : 0 < b) (m n : ℕ) (i : Fin m) {t : ℕ} (ht : t < n) :
    ∀ᵐ ω ∂law, |stopped b m n i (t + 1) ω - stopped b m n i t ω| ≤ b := by
  rw [stopped_eq (Nat.succ_le_of_lt ht), stopped_eq ht.le]
  exact site_inc_ae hb m i t

/-- The brackets up to time `n` of the continuations are those of the sites. -/
lemma predBracket_stopped (b : ℝ) (m n : ℕ) (i j : Fin m) :
    CERW.predBracket law filt (stopped b m n i) (stopped b m n j) n
      =ᵐ[law] CERW.predBracket law filt (site b m i) (site b m j) n :=
  CERW.Support.Lower.predBracket_congr_ae
    (ae_of_all _ fun ω t ht => by rw [stopped_eq ht])
    (ae_of_all _ fun ω t ht => by rw [stopped_eq ht])

end

end CERW.Support.Guards.CoinSites
