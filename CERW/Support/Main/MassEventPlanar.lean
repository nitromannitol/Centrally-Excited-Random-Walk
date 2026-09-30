import CERW.Support.Main.Event
import CERW.Support.Contact.ContactSetup
import CERW.Support.Contact.MassPlanar
import CERW.Support.Contact.EnvelopeShell
import CERW.Support.LocalTime.Bracket
import CERW.Support.Occupation.CellNorm
import CERW.Support.Main.ScaleLimits

/-!
# The mass step on the event, in the plane

For `d = 2` and all large `n`, `fluctEvent` gives `m ≤ C N^d Q` and `ℓ_n ≤ C (b - |·|)_+ + C W`,
where `b` is the inradius of `D_n` and `W = N Q^{1/d}`.
1. `D_n ⊆ B(0, H_n + √d) ⊆ B(0, R)` with `R = (C₀ + 1) N` (`cellSet_subset_ball`), so
   `exists_contact_setup` gives `b > 0`, `y₀`, `z` and `Δ ≤ C ε log(R + 2) ≤ C L`.
2. The global clause with `error_scale_le` gives `δ₀ ≤ C √N L` on `B(0, K N)`, `K = C₀ + 3`.
3. At `z`, the pointwise and local-martingale clauses, with `sum_range_eq_sum_localTime`, give
   `0 = ℓ_n(z) = U(z) + ρ - M` with `|ρ| + |M| ≤ C (√(B_z L) + L)`.
4. `exists_mass_planar` gives the claim once `L ≥ 1`, `L^6 ≤ N` and `Δ ≤ C √N`.
-/

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW CERW.Support.Law

variable {d : ℕ}

/-- `n / n^{1/3}` tends to infinity. -/
private lemma tendsto_natCast_div_natCast_rpow_three :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 3))
      Filter.atTop Filter.atTop := by
  have hexp : (0 : ℝ) < 1 - (1 : ℝ) / 3 := by norm_num
  have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (1 : ℝ) / 3))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr' ?_ htend
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_sub hnpos, Real.rpow_one]

/-- The mass step on the event for `d = 2`: the excess volume over the inradius ball is at most
`C N^d Q`, and `ℓ_n ≤ C (b - |·|)_+ + C N Q^{1/d}`. -/
theorem exists_mass_of_event_planar (hd : d = 2) {ε : ℝ} (hε : 0 < ε) {b : Site d → ℝ}
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
  subst hd
  obtain ⟨Cc, hCc, hcontact⟩ :=
    CERW.Support.Contact.exists_contact_setup (d := 2) (by norm_num : 2 ≤ 2)
  obtain ⟨Cm, hCmpos, hmassplanar⟩ :=
    CERW.Support.Contact.exists_mass_planar (K := C₀ + 3)
      (C₀ := max (C₁ * (Real.sqrt C₀ + 1)) 1) (C₁ := 2 * C₁) hε
      (by linarith) (le_trans zero_le_one (le_max_right _ _)) (by positivity)
  have hsqrt2_ev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
    have hNtend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
        tendsto_natCast_atTop_atTop
    exact hNtend.eventually_ge_atTop (Real.sqrt 2)
  have hL6_ev : ∀ᶠ n : ℕ in Filter.atTop,
      (Real.log (n + 2)) ^ 6 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
    have hlim := tendsto_log_rpow_div_rpow ((6 : ℕ) : ℝ) (c := (1 : ℝ) / 3) (by norm_num)
    have hle := hlim.eventually_le_const (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [hle, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnpos _
    rw [Real.rpow_natCast, div_le_iff₀ hNpos] at hn
    simpa using hn
  have hRN_ev : ∀ᶠ n : ℕ in Filter.atTop,
      (C₀ + 1) * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (n : ℝ) := by
    have hge := tendsto_natCast_div_natCast_rpow_three.eventually_ge_atTop (C₀ + 1)
    filter_upwards [hge, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnpos _
    have hmul := mul_le_mul_of_nonneg_right hn hNpos.le
    rw [div_mul_cancel₀ _ hNpos.ne'] at hmul
    exact hmul
  have hCN_ev : ∀ᶠ n : ℕ in Filter.atTop,
      (C₀ + 3) * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 * (n : ℝ) := by
    have hge := tendsto_natCast_div_natCast_rpow_three.eventually_ge_atTop ((C₀ + 3) / 2)
    filter_upwards [hge, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnpos _
    have hmul := mul_le_mul_of_nonneg_right hn hNpos.le
    rw [div_mul_cancel₀ _ hNpos.ne'] at hmul
    linarith
  have hlog_ratio : ∀ᶠ n : ℕ in Filter.atTop,
      Cc * ε * Real.log (n + 2) ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := by
    have hlim := tendsto_log_rpow_div_rpow (1 : ℝ) (c := (1 : ℝ) / 6) (by norm_num)
    have hle := hlim.eventually_le_const (show (0 : ℝ) < 1 / (Cc * ε + 1) by positivity)
    filter_upwards [hle, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnnonneg : (0 : ℝ) ≤ n := hnpos.le
    have hpowpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hnpos _
    have hlog : Real.log (n + 2) ^ (1 : ℝ) = Real.log (n + 2) := Real.rpow_one _
    rw [hlog, div_le_iff₀ hpowpos] at hn
    have hcnonneg : 0 ≤ Cc * ε := mul_nonneg hCc hε.le
    have hcnnpos : 0 < Cc * ε + 1 := by positivity
    calc Cc * ε * Real.log (n + 2)
        ≤ Cc * ε * ((1 / (Cc * ε + 1)) * (n : ℝ) ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left hn hcnonneg
      _ = (Cc * ε / (Cc * ε + 1)) * (n : ℝ) ^ ((1 : ℝ) / 6) := by ring
      _ ≤ 1 * (n : ℝ) ^ ((1 : ℝ) / 6) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnnonneg _)
          rw [div_le_one hcnnpos]
          linarith
      _ = (n : ℝ) ^ ((1 : ℝ) / 6) := one_mul _
  have hlog_ev : ∀ᶠ n : ℕ in Filter.atTop,
      Cc * ε * Real.log ((C₀ + 1) * (n : ℝ) ^ ((1 : ℝ) / 3) + 2)
        ≤ Real.sqrt ((n : ℝ) ^ ((1 : ℝ) / 3)) := by
    filter_upwards [hlog_ratio, hRN_ev, Filter.eventually_ge_atTop (1 : ℕ)] with n hratio hRN hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have harg : (C₀ + 1) * (n : ℝ) ^ ((1 : ℝ) / 3) + 2 ≤ n + 2 := by linarith
    have hlogmono : Real.log ((C₀ + 1) * (n : ℝ) ^ ((1 : ℝ) / 3) + 2)
        ≤ Real.log (n + 2) := Real.log_le_log (by positivity) harg
    have hsqrt_eq : Real.sqrt ((n : ℝ) ^ ((1 : ℝ) / 3)) = (n : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
      congr 1
      norm_num
    rw [hsqrt_eq]
    exact (mul_le_mul_of_nonneg_left hlogmono (mul_nonneg hCc hε.le)).trans hratio
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop (1 : ℕ)).and
      (hsqrt2_ev.and (hL6_ev.and (hCN_ev.and (hRN_ev.and hlog_ev)))))
  refine ⟨max (4 * ε) Cm, ?_, n₀, ?_⟩
  · exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * ε) (le_max_left _ _)
  · intro Ω X ω n hn
    obtain ⟨hn1, hsqrt2, hL6, hCN, hRN, hlog⟩ := hn₀ n hn
    dsimp only
    intro hE
    dsimp only [fluctEvent] at hE
    obtain ⟨⟨h0, hstep⟩, hcard, hMtime, hH, hint, hglob, hpt, hmart, hquad, hvec, hrad⟩ :=
      hE
    set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (2 + 1)) with hN
    set L : ℝ := Real.log (n + 2) with hL
    set binr : ℝ :=
      sInf ((fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖) '' (cellSet (fun j => X j ω) n)ᶜ)
      with hbinr
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : 0 < N := by rw [hN]; exact Real.rpow_pos_of_pos hnpos _
    have hNnonneg : 0 ≤ N := hNpos.le
    have hN3 : N = (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [hN]
      congr 1
      norm_num
    have hs2 : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hLpos : 0 < L := by
      rw [hL]
      exact Real.log_pos (by linarith only [hn1R])
    have hL1 : 1 ≤ L := by
      rw [hL]
      have h1log3 : (1 : ℝ) < Real.log 3 :=
        (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
      have hlog3 : Real.log 3 ≤ Real.log (n + 2) :=
        Real.log_le_log (by norm_num) (by linarith only [hn1R])
      exact le_of_lt (lt_of_lt_of_le h1log3 hlog3)
    have hN1 : 1 ≤ N := by
      rw [hN3]
      exact le_trans (by norm_num : (1 : ℝ) ≤ Real.sqrt 2) hsqrt2
    have hL6' : L ^ 6 ≤ N := by rw [hL, hN3]; exact hL6
    have hCN' : (C₀ + 3) * N ≤ 2 * (n : ℝ) := by rw [hN3]; exact hCN
    have hRN' : (C₀ + 1) * N ≤ (n : ℝ) := by rw [hN3]; exact hRN
    have hsqrt2' : Real.sqrt 2 ≤ N := by rw [hN3]; exact hsqrt2
    have hlog' : Cc * ε * Real.log ((C₀ + 1) * N + 2) ≤ Real.sqrt N := by
      rw [hN3]; exact hlog
    have hR1 : 1 ≤ (C₀ + 1) * N := by
      have hC1 : (1 : ℝ) ≤ C₀ + 1 := by linarith only [hC₀]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (C₀ + 1) * N := mul_le_mul hC1 hN1 zero_le_one (by linarith only [hC₀])
    have hDsub_R : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((C₀ + 1) * N) := by
      refine (CERW.Support.Occupation.cellSet_subset_ball (by norm_num : 1 ≤ 2)
        (fun j => X j ω) n).trans ?_
      apply Metric.ball_subset_ball
      have hH' : maxRadius (fun j => X j ω) n ≤ C₀ * N := by rw [hN]; exact hH
      rw [hs2]
      nlinarith only [hH', hsqrt2']
    obtain ⟨hbinrpos, hball, y₀, hy₀, z, hz0, hbz, hzupper, hmod0⟩ :=
      hcontact ε hε.le (fun j => X j ω) n ((C₀ + 1) * N) hn1 h0 hR1 hDsub_R
    have hbinr_le_R : binr ≤ (C₀ + 1) * N := by
      rw [hbinr]
      haveI : Nonempty (Fin 2) := ⟨⟨0, by norm_num⟩⟩
      have hRpos : 0 < (C₀ + 1) * N := lt_of_lt_of_le zero_lt_one hR1
      obtain ⟨y₁, hy₁⟩ :=
        (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 2)))
          (r := (C₀ + 1) * N)).mpr hRpos.le
      have hy₁norm : ‖y₁‖ = (C₀ + 1) * N := by simpa using (mem_sphere_iff_norm.mp hy₁)
      refine csInf_le ⟨0, ?_⟩ ⟨y₁, ?_, hy₁norm⟩
      · rintro r ⟨y, -, rfl⟩
        exact norm_nonneg y
      · intro hycell
        have hmem := hDsub_R hycell
        rw [Metric.mem_ball, dist_zero_right, hy₁norm] at hmem
        linarith only [hmem]
    have hz_le_K : euclidNorm z ≤ (C₀ + 3) * N := by
      have hzupper' := hzupper
      rw [hs2] at hzupper'
      have h1 : euclidNorm z ≤ (C₀ + 1) * N + Real.sqrt 2 / 2 :=
        by linarith only [hzupper', hbinr_le_R]
      have h2 : Real.sqrt 2 / 2 ≤ N := by
        have hle : Real.sqrt 2 / 2 ≤ Real.sqrt 2 := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          linarith only [Real.sqrt_nonneg (2 : ℝ)]
        linarith only [hle, hsqrt2']
      have h3 : (C₀ + 1) * N + N = (C₀ + 2) * N := by ring
      have h4 : (C₀ + 2) * N ≤ (C₀ + 3) * N := by
        have : (C₀ + 2 : ℝ) ≤ C₀ + 3 := by linarith only
        exact mul_le_mul_of_nonneg_right this hNnonneg
      linarith only [h1, h2, h3, h4]
    have hz3 : euclidNorm z ≤ 3 * (n : ℝ) := by linarith only [hz_le_K, hCN']
    have hzn : euclidNorm z < (C₀ + 3) * N := by
      have hzupper' := hzupper
      rw [hs2] at hzupper'
      have h1 : euclidNorm z ≤ (C₀ + 1) * N + Real.sqrt 2 / 2 :=
        by linarith only [hzupper', hbinr_le_R]
      have h2 : Real.sqrt 2 / 2 < 2 * N := by
        have hle : Real.sqrt 2 / 2 ≤ Real.sqrt 2 := by
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          linarith only [Real.sqrt_nonneg (2 : ℝ)]
        linarith only [hle, hsqrt2', hNpos]
      have h3 : (C₀ + 1) * N + 2 * N = (C₀ + 3) * N := by ring
      linarith only [h1, h2, h3]
    set δ₀ : ℝ := C₁ * (Real.sqrt (maxLocalTime (fun j => X j ω) n) * L + L) with hδ₀
    have hδ : δ₀ ≤ max (C₁ * (Real.sqrt C₀ + 1)) 1 * Real.sqrt N * L := by
      rw [hδ₀]
      have hMnn : 0 ≤ (maxLocalTime (fun j => X j ω) n : ℝ) := Nat.cast_nonneg _
      have hMle : (maxLocalTime (fun j => X j ω) n : ℝ) ≤ C₀ * N := by
        rw [hN]; exact hMtime
      obtain ⟨h1, -⟩ := CERW.Support.Contact.error_scale_le hMnn hC₀.le hMle hN1 hL1
      have hcoef : C₁ * (Real.sqrt C₀ + 1) ≤ max (C₁ * (Real.sqrt C₀ + 1)) 1 :=
        le_max_left _ _
      calc C₁ * (Real.sqrt (maxLocalTime (fun j => X j ω) n) * L + L)
          ≤ C₁ * ((Real.sqrt C₀ + 1) * (Real.sqrt N * L)) :=
            mul_le_mul_of_nonneg_left h1 hC₁.le
        _ = C₁ * (Real.sqrt C₀ + 1) * (Real.sqrt N * L) := by ring
        _ ≤ max (C₁ * (Real.sqrt C₀ + 1)) 1 * (Real.sqrt N * L) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = max (C₁ * (Real.sqrt C₀ + 1)) 1 * Real.sqrt N * L := by ring
    have happrox : ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ < (C₀ + 3) * N →
        |cellLocalTime (fun j => X j ω) n y - potential 2 ε (cellSet (fun j => X j ω) n) y|
          ≤ δ₀ := by
      intro y hy
      rw [hδ₀]
      have hy2n : ‖y‖ ≤ 2 * (n : ℝ) := by
        have : ‖y‖ < 2 * (n : ℝ) := lt_of_lt_of_le hy (by linarith only [hCN'])
        linarith only [this]
      exact hglob y hy2n
    set Mz : ℝ := dynkin ε (fun w => b (w - z)) X n ω with hMz
    set ρ : ℝ := (localTime (fun j => X j ω) n z : ℝ)
      - potential 2 ε (cellSet (fun j => X j ω) n) (toSpace z) + Mz with hρ
    have hptz : (localTime (fun j => X j ω) n z : ℝ)
        = potential 2 ε (cellSet (fun j => X j ω) n) (toSpace z) + ρ - Mz := by
      rw [hρ]; ring
    have hρ_le : |ρ| ≤ C₁ * L := by
      have h := hpt z hz3
      rw [hρ, hMz]
      exact h
    set Bz : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n,
        (localTime (fun j => X j ω) n x : ℝ) *
          (1 + euclidNorm (x - z)) ^ (-2 : ℝ) with hBz
    have hMz_le : |Mz| ≤ C₁ * (Real.sqrt (Bz * L) + L) := by
      have h := hmart z hz3
      have hsum := CERW.Support.LocalTime.sum_range_eq_sum_localTime (fun j => X j ω) n
        (fun x => (1 + euclidNorm (x - z)) ^ (2 - 2 * ((2 : ℕ) : ℝ)))
      rw [hsum] at h
      have hBz_eq : (∑ x ∈ departureRange (fun j => X j ω) n,
          (localTime (fun j => X j ω) n x : ℝ) *
            (1 + euclidNorm (x - z)) ^ (2 - 2 * ((2 : ℕ) : ℝ))) = Bz := by
        rw [hBz]
        apply Finset.sum_congr rfl
        intro x hx
        rw [show (2 : ℝ) - 2 * ((2 : ℕ) : ℝ) = (-2 : ℝ) by norm_num]
      rw [hBz_eq] at h
      rw [← hMz] at h
      exact h
    have hρM : |ρ| + |Mz| ≤ (2 * C₁) * (Real.sqrt (Bz * L) + L) := by
      have hsqrtnn : 0 ≤ Real.sqrt (Bz * L) := Real.sqrt_nonneg _
      calc |ρ| + |Mz| ≤ C₁ * L + C₁ * (Real.sqrt (Bz * L) + L) := add_le_add hρ_le hMz_le
        _ = C₁ * (Real.sqrt (Bz * L) + 2 * L) := by ring
        _ ≤ C₁ * (2 * (Real.sqrt (Bz * L) + L)) := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              linarith only [hsqrtnn]
        _ = (2 * C₁) * (Real.sqrt (Bz * L) + L) := by ring
    set Δ : ℝ := |potential 2 ε (cellSet (fun j => X j ω) n) y₀
        - potential 2 ε (cellSet (fun j => X j ω) n) (toSpace z)| with hΔdef
    have hmod : |potential 2 ε (cellSet (fun j => X j ω) n) y₀
        - potential 2 ε (cellSet (fun j => X j ω) n) (toSpace z)| ≤ Δ := by
      rw [hΔdef]
    have hΔ : Δ ≤ max (C₁ * (Real.sqrt C₀ + 1)) 1 * Real.sqrt N := by
      rw [hΔdef]
      have hle1 : |potential 2 ε (cellSet (fun j => X j ω) n) y₀
          - potential 2 ε (cellSet (fun j => X j ω) n) (toSpace z)| ≤ Real.sqrt N :=
        le_trans hmod0 hlog'
      have hcoef1 : (1 : ℝ) ≤ max (C₁ * (Real.sqrt C₀ + 1)) 1 := le_max_right _ _
      calc |potential 2 ε (cellSet (fun j => X j ω) n) y₀
            - potential 2 ε (cellSet (fun j => X j ω) n) (toSpace z)|
          ≤ Real.sqrt N := hle1
        _ = 1 * Real.sqrt N := (one_mul _).symm
        _ ≤ max (C₁ * (Real.sqrt C₀ + 1)) 1 * Real.sqrt N :=
            mul_le_mul_of_nonneg_right hcoef1 (Real.sqrt_nonneg N)
    have hDsub_K : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((C₀ + 3 - 1) * N) := by
      refine hDsub_R.trans (Metric.ball_subset_ball ?_)
      exact mul_le_mul_of_nonneg_right (by linarith only : C₀ + 1 ≤ C₀ + 3 - 1) hNpos.le
    obtain ⟨hmass1, hmass2⟩ := hmassplanar (fun j => X j ω) n binr N L δ₀ Δ ρ Mz z y₀
      hL1 hL6' hbinrpos hball hDsub_K hδ happrox hy₀ hz0 hbz hzn hmod hΔ hptz hρM
    constructor
    · have hcoef : Cm ≤ max (4 * ε) Cm := le_max_right _ _
      have hQnn : 0 ≤ N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg hLpos.le hNpos.le) _)
      calc (volume (cellSet (fun j => X j ω) n
            \ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) binr)).toReal
          ≤ Cm * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) := hmass1
        _ = Cm * (N ^ 2 * (L / N) ^ ((1 : ℝ) / 2)) := by ring
        _ ≤ max (4 * ε) Cm * (N ^ 2 * (L / N) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hcoef hQnn
        _ = max (4 * ε) Cm * N ^ 2 * (L / N) ^ ((1 : ℝ) / 2) := by ring
    · intro y
      have h := hmass2 y
      have hmaxnn : 0 ≤ max (binr - euclidNorm y) 0 := le_max_right _ _
      have hεC : 4 * ε ≤ max (4 * ε) Cm := le_max_left _ _
      have hCmC : Cm ≤ max (4 * ε) Cm := le_max_right _ _
      set Xq : ℝ := ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) with hXq
      have hXqnn : 0 ≤ Xq := by
        rw [hXq]
        exact Real.rpow_nonneg (Real.rpow_nonneg (div_nonneg hLpos.le hNpos.le) _) _
      have h1 : 4 * ε * max (binr - euclidNorm y) 0
          ≤ max (4 * ε) Cm * max (binr - euclidNorm y) 0 :=
        mul_le_mul_of_nonneg_right hεC hmaxnn
      have h2 : Cm * N * Xq ≤ max (4 * ε) Cm * N * Xq := by
        have hb := mul_le_mul_of_nonneg_right hCmC (mul_nonneg hNpos.le hXqnn)
        calc Cm * N * Xq = Cm * (N * Xq) := by ring
          _ ≤ max (4 * ε) Cm * (N * Xq) := hb
          _ = max (4 * ε) Cm * N * Xq := by ring
      calc (localTime (fun j => X j ω) n y : ℝ)
          ≤ 4 * ε * max (binr - euclidNorm y) 0 + Cm * N * Xq := by
            rw [hXq]
            exact h
        _ ≤ max (4 * ε) Cm * max (binr - euclidNorm y) 0 + max (4 * ε) Cm * N * Xq :=
            by linarith only [h1, h2]
        _ = max (4 * ε) Cm * max (binr - euclidNorm y) 0
              + max (4 * ε) Cm * N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
            rw [hXq]

end CERW.Support.Main
