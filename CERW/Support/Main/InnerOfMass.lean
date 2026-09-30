import CERW.Support.Main.Event
import CERW.Support.Main.InnerClauses
import CERW.Support.Contact.ContactSetup
import CERW.Support.Contact.Inradius
import CERW.Support.Contact.EnvelopeShell
import CERW.Support.Occupation.CellNorm

/-!
# The inner clauses on the event, given the mass bound

For all large `n`, on `fluctEvent`, let `b` be the inradius of `D_n` and suppose the excess
volume satisfies `m ≤ Cm N^d Q`.
1. `exists_contact_setup` with `R = (C₀ + 1) N` gives `b > 0`, `B(0, b) ⊆ D_n` and an unvisited
   site `z` with `|z| ≤ b + √d/2`.
2. `exists_inradius` with `K = C₀ + 2` gives `|b/N - a| ≤ C Q`, using the coarse, path and
   quadratic clauses.
3. The global clause with `error_scale_le` gives `δ₀ ≤ C N Q^{1/d}` on `B(0, K' N)`, with
   `K' = a + C₀ + 3`. Then `exists_inner_clauses` gives the inner inclusion, `A_n ⊆ V_n`, the
   volume and profile clauses, and `z ∉ A_n` with `|z| < aN + C N Q`.
-/

namespace CERW.Support.Main

open Filter Topology MeasureTheory LatticeProb CERW
open scoped symmDiff Pointwise

variable {d : ℕ}

/-- Eventually `K ≤ N`, `L³ ≤ N`, `N² ≤ n` and `1 ≤ n`, where `N = n^{1/(d+1)}` and
`L = log(n + 2)`. -/
private lemma eventually_scales (hd : 1 ≤ d) (K : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    K ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
    Real.log (n + 2) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ 2 ≤ n ∧ 1 ≤ n := by
  have hc : (0 : ℝ) < 1 / (d + 1) := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  have h2 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (3 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < 1 :=
    (tendsto_log_rpow_div_rpow 3 hc).eventually_lt_const one_pos
  have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hK, hL, h1n⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨hK, ?_, ?_, h1n⟩
  · rw [div_lt_one hNpos] at hL
    have e : Real.log (n + 2) ^ (3 : ℕ) = Real.log (n + 2) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e]; exact hL.le
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (n : ℝ) ^ ((1 : ℝ) / (d + 1) * ((2 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hn1
          have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          push_cast
          linarith
      _ = n := Real.rpow_one _


/-- The error scale of the global approximation is at most `2 (√C₀ + 1) N Q^{1/d}` once `1 ≤ L`,
`L³ ≤ N` and `M ≤ C₀ N`. -/
private lemma error_le_scale (hd : 2 ≤ d) {M C₀ N L : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (hL : 1 ≤ L) (hLN : L ^ 3 ≤ N) (hMN : M ≤ C₀ * N) :
    (if d = 2 then Real.sqrt M * L + L else Real.sqrt (M * L) + L) ≤
      2 * (Real.sqrt C₀ + 1) * (N * (if d = 2 then (L / N) ^ ((1 : ℝ) / 2)
        else (L / N) ^ ((d : ℝ) / (2 * d - 1))) ^ ((1 : ℝ) / d)) := by
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hN1 : 1 ≤ N := hL3.trans hLN
  have hN : 0 < N := by linarith
  have hLN' : L ≤ N := (le_self_pow₀ hL (by norm_num)).trans hLN
  have ht : 0 < L / N := div_pos (by linarith) hN
  have ht1 : L / N ≤ 1 := (div_le_one hN).2 hLN'
  obtain ⟨h2e, h3e⟩ := CERW.Support.Contact.error_scale_le hM hC₀ hMN hN1 hL
  have hs : 0 ≤ Real.sqrt C₀ + 1 := by positivity
  split_ifs with h2
  · subst h2
    have key : Real.sqrt N * L ≤ N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) := by
      have hq : ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) =
          (L / N) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_mul ht.le]; norm_num
      rw [hq]
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
      have h4 : ((L / N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = L / N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
      have hsN : Real.sqrt N ^ (4 : ℕ) = N ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hN.le]
      rw [mul_pow, mul_pow, h4, hsN]
      have e : N ^ 4 * (L / N) = N ^ 3 * L := by field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hLN (by positivity : 0 ≤ N ^ 2 * L)
      nlinarith
    calc Real.sqrt M * L + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt N * L) := h2e
      _ ≤ (Real.sqrt C₀ + 1) * (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ 2 * (Real.sqrt C₀ + 1) *
            (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
          have : 0 ≤ (Real.sqrt C₀ + 1) *
              (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by positivity
          linarith
  · have hd3 : (3 : ℝ) ≤ d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hexp : (d : ℝ) / (2 * d - 1) * (1 / d) ≤ 1 / 2 := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    have hQ : (L / N) ^ ((1 : ℝ) / 2) ≤ ((L / N) ^ ((d : ℝ) / (2 * d - 1))) ^ ((1 : ℝ) / d) := by
      rw [← Real.rpow_mul ht.le]
      exact Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp
    have hsq : Real.sqrt (N * L) = N * (L / N) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, show N * L = N ^ 2 * (L / N) by field_simp,
        Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
    have hLsq : L ≤ Real.sqrt (N * L) := by
      calc L = Real.sqrt (L * L) := (Real.sqrt_mul_self (by linarith)).symm
        _ ≤ Real.sqrt (N * L) := Real.sqrt_le_sqrt (by nlinarith)
    calc Real.sqrt (M * L) + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt (N * L) + L) := h3e
      _ ≤ (Real.sqrt C₀ + 1) * (2 * Real.sqrt (N * L)) := by gcongr; linarith
      _ = 2 * (Real.sqrt C₀ + 1) * (N * (L / N) ^ ((1 : ℝ) / 2)) := by rw [hsq]; ring
      _ ≤ 2 * (Real.sqrt C₀ + 1) *
            (N * ((L / N) ^ ((d : ℝ) / (2 * d - 1))) ^ ((1 : ℝ) / d)) := by gcongr


/-- On the event, a mass bound `m ≤ Cm N^d Q` gives the inradius estimate, the inner inclusion,
`A_n ⊆ V_n`, the volume and profile clauses, and an unvisited site of norm less than
`a N + C N Q`. -/
theorem exists_inner_of_mass (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {b : Site d → ℝ}
    {C₀ C₁ Cm : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCm : 0 ≤ Cm) {bd r₀ : ℕ} :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
      let Y : ℕ → Site d := fun j => X j ω
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let binr : ℝ := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet Y n)ᶜ)
      fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
      (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) binr)).toReal
        ≤ Cm * N ^ d * Q →
        |binr / N - a| ≤ C * Q ∧
        {x : Site d | euclidNorm x < (a - C * Q) * N} ⊆ ↑(departureRange Y n) ∧
        (↑(departureRange Y n) : Set (Site d)) ⊆ ↑(visitedRange Y n) ∧
        volume ((N⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
            + ENNReal.ofReal |((departureRange Y n).card : ℝ) / N ^ d - ωd * a ^ d|
          ≤ ENNReal.ofReal (C * Q) ∧
        (∀ x : Site d,
          |(localTime Y n x : ℝ) / N - 2 * d * ε * max (a - euclidNorm x / N) 0|
            ≤ C * Q ^ ((1 : ℝ) / d)) ∧
        ∃ x : Site d, x ∉ departureRange Y n ∧ euclidNorm x < a * N + C * N * Q := by
  intro ωd a
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hωpos : 0 < ωd := unitBallVolume_pos d
  have ha : 0 < a := Real.rpow_pos_of_pos
    (div_pos (by positivity) (mul_pos (mul_pos (by positivity) hε) hωpos)) _
  obtain ⟨Cc, -, hcs⟩ := CERW.Support.Contact.exists_contact_setup hd
  obtain ⟨Ci, hCi, ni, hir⟩ := CERW.Support.Contact.exists_inradius hd hε (K := C₀ + 2)
    (by linarith) (C₁ := max Cm C₁) (le_max_of_le_left hCm)
  have hC₂ : 0 ≤ max Ci (max Cm (2 * (Real.sqrt C₀ + 1) * C₁)) := le_max_of_le_left hCi.le
  obtain ⟨Cq, hCq, nq, hic⟩ := exists_inner_clauses hd hε hC₂ (K := a + C₀ + 3)
    (show a + 1 ≤ a + C₀ + 3 by linarith)
  obtain ⟨ns, hns⟩ := eventually_scales hd1 (max (a + C₀ + 3) (Real.sqrt d + 1))
  refine ⟨max Ci Cq, lt_max_of_lt_left hCi, max (max ni nq) ns, fun X ω n hn => ?_⟩
  have hni : ni ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnq : nq ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnsn : ns ≤ n := le_trans (le_max_right _ _) hn
  intro Y N L Q binr hE hm
  dsimp only [fluctEvent] at hE
  obtain ⟨⟨h0, -⟩, hcard, hM, hH, -, hglob, -, -, hquad, -, -⟩ := hE
  obtain ⟨hKN, hL3, hN2, h1n⟩ := hns n hnsn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hsd : Real.sqrt d + 1 ≤ N := (le_max_right _ _).trans hKN
  have hK'N : a + C₀ + 3 ≤ N := (le_max_left _ _).trans hKN
  have hN1 : 1 ≤ N := by linarith [Real.sqrt_nonneg (d : ℝ)]
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ L := by
    show 1 ≤ Real.log (n + 2)
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9]
  have hQ : 0 ≤ Q := by
    show (0 : ℝ) ≤ if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
    split_ifs <;> exact Real.rpow_nonneg (div_nonneg (by linarith) hN0.le) _
  have hQd : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQ _
  have hNd : 0 ≤ N ^ d := pow_nonneg hN0.le d
  have hC₀N : 0 ≤ C₀ * N := mul_nonneg hC₀.le hN0.le
  have hD : cellSet Y n ⊆ Metric.ball 0 ((C₀ + 1) * N) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n).trans
      (Metric.ball_subset_ball (by linarith [Real.sqrt_nonneg (d : ℝ)]))
  obtain ⟨hb, hball, y₀, -, z, hz0, -, hzb, -⟩ :=
    hcs ε hε.le Y n ((C₀ + 1) * N) h1n h0 (by linarith) hD
  have hXn : euclidNorm (X n ω) ≤ (C₀ + 2) * N :=
    (euclidNorm_le_maxRadius Y (le_refl n)).trans (by linarith)
  have hrad : |binr / N - a| ≤ Ci * Q :=
    hir X ω n binr hni h0 hb.le hball
      (hD.trans ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall))
      hXn (hcard.trans (mul_le_mul_of_nonneg_right (by linarith) hNd))
      (hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hNd) hQ))
      (hquad.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  have hMn : (0 : ℝ) ≤ (maxLocalTime Y n : ℝ) := Nat.cast_nonneg _
  have herr := error_le_scale hd hMn hC₀.le hL1 hL3 hM
  have hδ : C₁ * (if d = 2 then Real.sqrt (maxLocalTime Y n : ℝ) * L + L
      else Real.sqrt ((maxLocalTime Y n : ℝ) * L) + L)
      ≤ max Ci (max Cm (2 * (Real.sqrt C₀ + 1) * C₁)) * N * Q ^ ((1 : ℝ) / d) := by
    have h3 : 2 * (Real.sqrt C₀ + 1) * C₁ ≤ max Ci (max Cm (2 * (Real.sqrt C₀ + 1) * C₁)) :=
      (le_max_right _ _).trans (le_max_right _ _)
    have h4 : 0 ≤ N * Q ^ ((1 : ℝ) / d) := mul_nonneg hN0.le hQd
    calc C₁ * (if d = 2 then Real.sqrt (maxLocalTime Y n : ℝ) * L + L
          else Real.sqrt ((maxLocalTime Y n : ℝ) * L) + L)
        ≤ C₁ * (2 * (Real.sqrt C₀ + 1) * (N * Q ^ ((1 : ℝ) / d))) :=
          mul_le_mul_of_nonneg_left herr hC₁.le
      _ = 2 * (Real.sqrt C₀ + 1) * C₁ * (N * Q ^ ((1 : ℝ) / d)) := by ring
      _ ≤ max Ci (max Cm (2 * (Real.sqrt C₀ + 1) * C₁)) * (N * Q ^ ((1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_right h3 h4
      _ = max Ci (max Cm (2 * (Real.sqrt C₀ + 1) * C₁)) * N * Q ^ ((1 : ℝ) / d) := by ring
  have h2n : (a + C₀ + 3) * N ≤ 2 * n :=
    calc (a + C₀ + 3) * N ≤ N * N := mul_le_mul_of_nonneg_right hK'N hN0.le
      _ = N ^ 2 := (sq N).symm
      _ ≤ n := hN2
      _ ≤ 2 * n := by linarith
  obtain ⟨hin, hAV, hvol, hprof, hzA, hzn⟩ := hic Y n binr _ z hnq hb hball
    (hD.trans (Metric.ball_subset_ball (mul_le_mul_of_nonneg_right (by linarith) hN0.le)))
    (hrad.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ))
    (hm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_left Cm _).trans (le_max_right Ci _)) hNd) hQ))
    hδ (fun y hy => hglob y (by linarith)) hz0 hzb
  have hi : Ci ≤ max Ci Cq := le_max_left _ _
  have hq : Cq ≤ max Ci Cq := le_max_right _ _
  refine ⟨hrad.trans (mul_le_mul_of_nonneg_right hi hQ), fun y hy => hin ?_, hAV,
    hvol.trans ?_, fun y => (hprof y).trans ?_, z, hzA, hzn.trans_le ?_⟩
  · simp only [Set.mem_setOf_eq] at hy ⊢
    exact lt_of_lt_of_le hy (by gcongr)
  · exact ENNReal.ofReal_le_ofReal (by gcongr)
  · gcongr
  · gcongr

end CERW.Support.Main
