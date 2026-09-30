import CERW.Support.Main.Event
import CERW.Support.Contact.ContactSetup
import CERW.Support.Contact.MassHigh
import CERW.Support.LocalTime.Bracket
import CERW.Support.Occupation.CellNorm
import CERW.Support.Main.ScaleLimits

/-!
# The mass step on the event, in dimensions three and higher

For `d ≥ 3` and all large `n`, `fluctEvent` gives `m ≤ C N^d Q` and `ℓ_n ≤ C (b - |·|)_+ + C W`,
where `b` is the inradius of `D_n` and `W = N Q^{1/d}`.
1. `D_n ⊆ B(0, H_n + √d) ⊆ B(0, R)` with `R = (C₀ + 1) N` (`cellSet_subset_ball`), so
   `exists_contact_setup` gives `b > 0`, `y₀`, `z` and `Δ ≤ C ε log(R + 2) ≤ C L`.
2. The pointwise and local-martingale clauses, with `sum_range_eq_sum_localTime`, give the
   decomposition hypotheses of `exists_mass_high` at every site of norm at most `n`, with
   `M(y)` the local Dynkin martingale.
3. `exists_mass_high` with `K = C₀ + 3` gives the claim, once `L ≤ N`, `|z| ≤ n` and `|X_j| ≤ n`.
-/

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- `n / n^{1/(d+1)}` tends to infinity for `d ≥ 1`: its exponent `1 - 1/(d+1)` is positive. -/
private lemma tendsto_natCast_div_natCast_rpow (d : ℕ) (hd : 1 ≤ d) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
      Filter.atTop Filter.atTop := by
  have hexp : (0 : ℝ) < 1 - (1 : ℝ) / (d + 1) := by
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [sub_pos, div_lt_one (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
    linarith
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (1 : ℝ) / (d + 1)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr' ?_ htend
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_sub hnpos, Real.rpow_one]

/-- The mass step on the event for `d ≥ 3`: the excess volume over the inradius ball is at most
`C N^d Q`, and `ℓ_n ≤ C (b - |·|)_+ + C N Q^{1/d}`. -/
theorem exists_mass_of_event_high (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) {b : Site d → ℝ}
    {C₀ C₁ : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) {bd r₀ : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
      let Y : ℕ → Site d := fun j => X j ω
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let binr : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet Y n)ᶜ)
      fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
        (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) binr)).toReal
          ≤ C * N ^ d * Q ∧
        ∀ y : Site d, (localTime Y n y : ℝ) ≤
          C * max (binr - euclidNorm y) 0 + C * N * Q ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hdne2 : d ≠ 2 := by omega
  obtain ⟨Cc, hCc, hcontact⟩ := CERW.Support.Contact.exists_contact_setup (d := d) hd2
  obtain ⟨Cm, hCmpos, hmasshigh⟩ := CERW.Support.Contact.exists_mass_high (d := d) hd hε
    (K := C₀ + 3) (C₀ := Cc * ε) (C₁ := C₁)
    (by linarith) (mul_nonneg hCc hε.le) hC₁.le
  have hsqrt_ev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt d ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    have hNtend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (show 0 < (1 : ℝ) / (d + 1) by positivity)).comp
        tendsto_natCast_atTop_atTop
    exact hNtend.eventually_ge_atTop (Real.sqrt d)
  have hCN_ev : ∀ᶠ n : ℕ in Filter.atTop,
      (C₀ + 2) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ (n : ℝ) := by
    have hge := (tendsto_natCast_div_natCast_rpow d hd1).eventually_ge_atTop (C₀ + 2)
    filter_upwards [hge, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
    have := mul_le_mul_of_nonneg_right hn hNpos.le
    rw [div_mul_cancel₀ _ hNpos.ne'] at this
    exact this
  have hL_ev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n + 2) ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    have hlim := tendsto_log_rpow_div_rpow (1 : ℝ) (c := (1 : ℝ) / (d + 1)) (by positivity)
    have hle := hlim.eventually_le_const (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [hle, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
    rw [Real.rpow_one] at hn
    rw [div_le_iff₀ hNpos] at hn
    simpa using hn
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop (1 : ℕ)).and (hsqrt_ev.and (hCN_ev.and hL_ev)))
  refine ⟨Cm, hCmpos, n₀, ?_⟩
  intro Ω X ω n hn
  obtain ⟨hn1, hsqrt, hCN, hLN⟩ := hn₀ n hn
  dsimp only
  simp only [if_neg hdne2]
  intro hE
  dsimp only [fluctEvent] at hE
  obtain ⟨⟨h0, hstep⟩, hcard, hMtime, hH, hint, hglob, hpt, hmart, hquad, hvec, hrad⟩ := hE
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN
  set L : ℝ := Real.log (n + 2) with hL
  set Q : ℝ := (L / N) ^ ((d : ℝ) / (2 * d - 1)) with hQ
  set binr : ℝ :=
    sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet (fun j => X j ω) n)ᶜ)
    with hbinr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < N := by rw [hN]; exact Real.rpow_pos_of_pos hnpos _
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn1])
  have hQnonneg : 0 ≤ Q := by
    rw [hQ]
    exact Real.rpow_nonneg (div_nonneg hLpos.le hNnonneg) _
  have hsqrt' : Real.sqrt d ≤ N := by rw [hN]; exact hsqrt
  have hCN' : (C₀ + 2) * N ≤ (n : ℝ) := by rw [hN]; exact hCN
  have hLN' : L ≤ N := by rw [hL, hN]; exact hLN
  have hN1 : 1 ≤ N := by
    rw [hN]
    have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h1n
      (by positivity : (0 : ℝ) ≤ (1 : ℝ) / (d + 1))
    simpa using this
  have hR1 : 1 ≤ (C₀ + 1) * N := by
    have hC1 : (1 : ℝ) ≤ C₀ + 1 := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C₀ + 1) * N := mul_le_mul hC1 hN1 zero_le_one (by linarith)
  have hDsub_R : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((C₀ + 1) * N) := by
    refine (CERW.Support.Occupation.cellSet_subset_ball hd1 (fun j => X j ω) n).trans ?_
    apply Metric.ball_subset_ball
    have hH' : maxRadius (fun j => X j ω) n ≤ C₀ * N := by
      rw [hN]
      exact hH
    linarith [hH', hsqrt']
  have hbinr_le_R : binr ≤ (C₀ + 1) * N := by
    rw [hbinr]
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have hRpos : 0 < (C₀ + 1) * N := lt_of_lt_of_le zero_lt_one hR1
    obtain ⟨y₁, hy₁⟩ :=
      (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin d)))
        (r := (C₀ + 1) * N)).mpr hRpos.le
    have hy₁norm : ‖y₁‖ = (C₀ + 1) * N := by simpa using (mem_sphere_iff_norm.mp hy₁)
    refine csInf_le ⟨0, ?_⟩ ⟨y₁, ?_, hy₁norm⟩
    · rintro r ⟨y, -, rfl⟩
      exact norm_nonneg y
    · intro hycell
      have hmem := hDsub_R hycell
      rw [Metric.mem_ball, dist_zero_right, hy₁norm] at hmem
      linarith
  obtain ⟨hbinrpos, hball, y₀, hy₀, z, hz0, hbz, hzupper, hmod0⟩ :=
    hcontact ε hε.le (fun j => X j ω) n ((C₀ + 1) * N) hn1 h0 hR1 hDsub_R
  have hlog_le : Real.log ((C₀ + 1) * N + 2) ≤ L := by
    rw [hL]
    apply Real.log_le_log
    · positivity
    · have hRle : (C₀ + 1) * N ≤ (n : ℝ) := by
        have hC1 : C₀ + 1 ≤ C₀ + 2 := by linarith
        have := mul_le_mul_of_nonneg_right hC1 hNnonneg
        linarith [this, hCN']
      linarith
  have hΔ : |potential d ε (cellSet (fun j => X j ω) n) y₀
      - potential d ε (cellSet (fun j => X j ω) n) (toSpace z)| ≤ (Cc * ε) * L := by
    have hεc : 0 ≤ Cc * ε := mul_nonneg hCc hε.le
    calc |potential d ε (cellSet (fun j => X j ω) n) y₀
          - potential d ε (cellSet (fun j => X j ω) n) (toSpace z)|
        ≤ Cc * ε * Real.log ((C₀ + 1) * N + 2) := hmod0
      _ ≤ Cc * ε * L := mul_le_mul_of_nonneg_left hlog_le hεc
  have hDsub_K : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 (((C₀ + 3) - 1) * N) := by
    refine (CERW.Support.Occupation.cellSet_subset_ball hd1 (fun j => X j ω) n).trans ?_
    apply Metric.ball_subset_ball
    have hH' : maxRadius (fun j => X j ω) n ≤ C₀ * N := by
      rw [hN]
      exact hH
    have hcoef : C₀ + 1 ≤ (C₀ + 3) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hNnonneg
    linarith [hH', hsqrt', hmul]
  have hzn : euclidNorm z ≤ (n : ℝ) := by
    have hRle : (C₀ + 1) * N ≤ (n : ℝ) := by
      have hC1 : C₀ + 1 ≤ C₀ + 2 := by linarith
      have := mul_le_mul_of_nonneg_right hC1 hNnonneg
      linarith [this, hCN']
    linarith [hzupper, hbinr_le_R, hsqrt', hNnonneg, hRle]
  have hXn : ∀ j < n, euclidNorm ((fun j => X j ω) j) ≤ (n : ℝ) := by
    intro j hj
    have h := CERW.Support.Occupation.euclidNorm_le_of_steps (fun j => X j ω) h0 hstep j
    have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_of_lt hj)
    linarith
  set M : Site d → ℝ := fun y => dynkin ε (fun z => b (z - y)) X n ω with hMdef
  have hpt' : ∀ y : Site d, euclidNorm y ≤ (n : ℝ) →
      |(localTime (fun j => X j ω) n y : ℝ)
        - potential d ε (cellSet (fun j => X j ω) n) (toSpace y) + M y| ≤ C₁ * L := by
    intro y hy
    have hy3 : euclidNorm y ≤ 3 * (n : ℝ) := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith
    have h := hpt y hy3
    rw [hL]
    simpa only [hMdef] using h
  have hmart' : ∀ y : Site d, euclidNorm y ≤ (n : ℝ) →
      |M y| ≤ C₁ * (Real.sqrt
        ((∑ x ∈ departureRange (fun j => X j ω) n,
          (localTime (fun j => X j ω) n x : ℝ) *
            (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * L) + L) := by
    intro y hy
    have hy3 : euclidNorm y ≤ 3 * (n : ℝ) := by
      have : (0 : ℝ) ≤ n := by positivity
      linarith
    have h := hmart y hy3
    rw [hL] at h
    rw [hMdef]
    have hsum := CERW.Support.LocalTime.sum_range_eq_sum_localTime (fun j => X j ω) n
      (fun x => (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
    rw [hsum] at h
    exact h
  have hmass := hmasshigh (fun j => X j ω) n binr N
    |potential d ε (cellSet (fun j => X j ω) n) y₀
      - potential d ε (cellSet (fun j => X j ω) n) (toSpace z)| M z y₀
    hn1 hXn hLN' hbinrpos hball hDsub_K hy₀ hz0 hbz hzn (le_refl _) hΔ hpt' hmart'
  rw [← hL] at hmass
  rw [← hQ] at hmass
  exact hmass

end CERW.Support.Main
