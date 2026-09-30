import CERW.Support.Main.Event
import CERW.Support.Main.OuterInclusion
import CERW.Support.Coarse.OuterEnvelope

/-!
# The outer inclusion on the event, given the mass bound

For all large `n`, on `fluctEvent`, let `b` be the inradius of `D_n`. Suppose that
`m ≤ Cm N^d Q`, `ℓ_n ≤ Cm (b - |·|)_+ + Cm N Q^{1/d}` and `|b/N - a| ≤ Cm Q`.
1. Since `Q → 0` and `a > 0`, `aN/2 ≤ b ≤ 2aN`.
2. `exists_outer_of_envelope` with `c₁ = a/2` and `c₂ = 2a`, using the path, vector, interval,
   radial and coarse clauses, gives `H_n ≤ b + C W L`.
3. `exists_outer_inclusion` then gives `V_n ⊆ {|x| < (a + C Q^{1/d} L) N}`.
-/

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- On positive arguments `s ≤ t` the weighted exterior volume does not increase, so the
difference `tail d D s - tail d D t` is nonnegative. -/
private lemma tail_sub_nonneg {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    0 ≤ tail d D s - tail d D t :=
  sub_nonneg.mpr (CERW.Support.Geometry.tail_antitoneOn hD hDb (Set.mem_Ioi.mpr hs)
    (Set.mem_Ioi.mpr (lt_of_lt_of_le hs hst)) hst)

/-- On the event, a mass bound, an envelope and the inradius estimate give the outer inclusion
`V_n ⊆ {|x| < (a + C Q^{1/d} L) N}`. -/
theorem exists_outer_of_mass (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {b : Site d → ℝ}
    {C₀ C₁ Cm : ℝ} (hC₀ : 0 < C₀) (hCm : 0 ≤ Cm) {bd r₀ : ℕ} (hbd : 1 ≤ bd) :
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
      (∀ y : Site d, (localTime Y n y : ℝ) ≤
        Cm * max (binr - euclidNorm y) 0 + Cm * N * Q ^ ((1 : ℝ) / d)) →
      |binr / N - a| ≤ Cm * Q →
        (↑(visitedRange Y n) : Set (Site d)) ⊆
          {x | euclidNorm x < (a + C * Q ^ ((1 : ℝ) / d) * L) * N} := by
  intro ωd a
  have hω : 0 < ωd := unitBallVolume_pos d
  have ha : 0 < a := by
    have h : a = ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) := rfl
    rw [h]
    exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨Ce, hCe_pos, ne, hEnv⟩ :=
    CERW.Support.Coarse.exists_outer_of_envelope (d := d) hd hε
      (C₁ := max C₀ C₁) (C₂ := Cm) (c₁ := a / 2) (c₂ := 2 * a)
      (lt_max_iff.mpr (Or.inl hC₀)) hCm (by linarith) (by linarith)
      (bd := bd) (r₀ := max r₀ (bd + 1)) hbd
  obtain ⟨Co, hCo_pos, no, hInc⟩ :=
    exists_outer_inclusion (d := d) hd (a := a) (C₂ := max Cm Ce)
      (le_trans hCm (le_max_left Cm Ce))
  have hQev : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ n ∧ Cm * (if d = 2 then
        (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^
          ((d : ℝ) / (2 * d - 1))) ≤ a / 2 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ),
      ((tendsto_rate_zero hd).const_mul Cm).eventually_lt_const
        (by linarith : Cm * 0 < a / 2)] with n hn1 hn2
    exact ⟨hn1, le_of_lt hn2⟩
  obtain ⟨nQ, hnQ⟩ := Filter.eventually_atTop.mp hQev
  refine ⟨Co, hCo_pos, max (max ne no) nQ, ?_⟩
  intro Ω X ω n hn Y N L Q binr hE hvol henv hba
  have hn_ne : ne ≤ n := le_trans (le_trans (le_max_left ne no) (le_max_left _ _)) hn
  have hn_no : no ≤ n := le_trans (le_trans (le_max_right ne no) (le_max_left _ _)) hn
  have hn_nQ : nQ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hn1, hQle⟩ := hnQ n hn_nQ
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < N := Real.rpow_pos_of_pos hnpos _
  have hLpos : 0 < L := by
    show 0 < Real.log (n + 2)
    exact Real.log_pos (by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith)
  have hQnonneg : 0 ≤ Q := by
    have hLN : 0 ≤ L / N := div_nonneg hLpos.le hNpos.le
    change 0 ≤ (if d = 2 then (L / N) ^ ((1 : ℝ) / 2)
      else (L / N) ^ ((d : ℝ) / (2 * d - 1)))
    split_ifs
    · exact Real.rpow_nonneg hLN _
    · exact Real.rpow_nonneg hLN _
  have hd1 : 1 ≤ d := by omega
  have hDmeas : MeasurableSet (cellSet Y n) :=
    CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDbdd : Bornology.IsBounded (cellSet Y n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius Y n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
  simp only [fluctEvent] at hE
  obtain ⟨⟨h0, hstep⟩, hcard, hM, hH, hint, hglob, hpt, hmart, hquad, hvec, hrad⟩ := hE
  have hbge : a / 2 * N ≤ binr := by
    have h1 : a - Cm * Q ≤ binr / N := by
      have h2 := (abs_le.mp hba).1
      linarith
    have h2 : a / 2 ≤ binr / N := by linarith
    calc a / 2 * N ≤ (binr / N) * N := mul_le_mul_of_nonneg_right h2 hNpos.le
      _ = binr := div_mul_cancel₀ binr hNpos.ne'
  have hble : binr ≤ 2 * a * N := by
    have h1 : binr / N ≤ a + Cm * Q := by
      have h2 := (abs_le.mp hba).2
      linarith
    have h2 : binr / N ≤ 2 * a := by linarith
    calc binr = (binr / N) * N := (div_mul_cancel₀ binr hNpos.ne').symm
      _ ≤ 2 * a * N := mul_le_mul_of_nonneg_right h2 hNpos.le
  have hM' : (maxLocalTime Y n : ℝ) ≤ max C₀ C₁ * N :=
    le_trans hM (mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) hNpos.le)
  have hvec' : ∀ s t : ℕ, s < t → t ≤ n →
      ‖Support.Coarse.compensated ε X t ω - Support.Coarse.compensated ε X s ω‖ ≤
        max C₀ C₁ * Real.sqrt (((t : ℝ) - s) * L) := by
    intro s t hst htn
    calc ‖Support.Coarse.compensated ε X t ω - Support.Coarse.compensated ε X s ω‖
        ≤ C₁ * Real.sqrt (((t : ℝ) - s) * L) := hvec s t hst htn
      _ ≤ max C₀ C₁ * Real.sqrt (((t : ℝ) - s) * L) :=
          mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) (Real.sqrt_nonneg _)
  have hint' : ∀ s t : ℕ, s < t → t ≤ n →
      (intervalMax Y s t : ℝ) ≤
        max C₀ C₁ * ε * (freshCount Y s t : ℝ) ^ ((1 : ℝ) / d) +
          max C₀ C₁ * (if d = 2 then L ^ 2 else L) := by
    intro s t hst htn
    have hfc : 0 ≤ (freshCount Y s t : ℝ) ^ ((1 : ℝ) / d) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hlam : 0 ≤ (if d = 2 then L ^ 2 else L) := by
      by_cases h2 : d = 2
      · rw [if_pos h2]; positivity
      · rw [if_neg h2]; exact hLpos.le
    calc (intervalMax Y s t : ℝ) ≤
          C₁ * ε * (freshCount Y s t : ℝ) ^ ((1 : ℝ) / d) +
            C₁ * (if d = 2 then L ^ 2 else L) := hint s t hst htn
      _ ≤ max C₀ C₁ * ε * (freshCount Y s t : ℝ) ^ ((1 : ℝ) / d) +
            max C₀ C₁ * (if d = 2 then L ^ 2 else L) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hε.le) hfc
          · exact mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hlam
  have hFsub : ∀ r : ℕ, bd + 1 ≤ r →
      0 ≤ tail d (cellSet Y n) ((r : ℝ) - bd) - tail d (cellSet Y n) ((r : ℝ) + bd) := by
    intro r hr
    have hrR : (bd : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have hs : 0 < (r : ℝ) - bd := by linarith
    have hst : (r : ℝ) - bd ≤ (r : ℝ) + bd := by
      have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg bd
      linarith
    exact tail_sub_nonneg hDmeas hDbdd hs hst
  have hrad' : ∀ r : ℕ, max r₀ (bd + 1) ≤ r → r ≤ n →
      tail d (cellSet Y n) ((r : ℝ) + bd) ≤
        max C₀ C₁ * (shellMax Y n r : ℝ) *
            (tail d (cellSet Y n) ((r : ℝ) - bd) - tail d (cellSet Y n) ((r : ℝ) + bd)) +
        max C₀ C₁ * (Real.sqrt ((maxLocalTime Y n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) *
            tail d (cellSet Y n) ((r : ℝ) - bd) * L) + (r : ℝ) ^ (1 - (d : ℝ)) * L) := by
    intro r hr0 hrn
    have hr0e : r₀ ≤ r := le_trans (le_max_left _ _) hr0
    have hrbd : bd + 1 ≤ r := le_trans (le_max_right _ _) hr0
    have hsub := hFsub r hrbd
    set Fm : ℝ := tail d (cellSet Y n) ((r : ℝ) - bd) with hFm
    set Fp : ℝ := tail d (cellSet Y n) ((r : ℝ) + bd) with hFp
    set R : ℝ := Real.sqrt ((maxLocalTime Y n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) * Fm * L) +
        (r : ℝ) ^ (1 - (d : ℝ)) * L with hR
    have hshell0 : 0 ≤ (shellMax Y n r : ℝ) := Nat.cast_nonneg _
    have hR0 : 0 ≤ R := by
      rw [hR]
      have h1 : 0 ≤ Real.sqrt ((maxLocalTime Y n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) * Fm * L) :=
        Real.sqrt_nonneg _
      have h2 : 0 ≤ (r : ℝ) ^ (1 - (d : ℝ)) * L :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) _) hLpos.le
      linarith
    have hA0 : 0 ≤ (shellMax Y n r : ℝ) * (Fm - Fp) + R :=
      add_nonneg (mul_nonneg hshell0 hsub) hR0
    have hbase := hrad r hr0e hrn
    have hbase' : tail d (cellSet Y n) ((r : ℝ) + bd) ≤
        C₁ * ((shellMax Y n r : ℝ) * (Fm - Fp) + R) := by
      calc tail d (cellSet Y n) ((r : ℝ) + bd)
          ≤ C₁ * (shellMax Y n r : ℝ) * (Fm - Fp) + C₁ * R := hbase
        _ = C₁ * ((shellMax Y n r : ℝ) * (Fm - Fp) + R) := by ring
    have hmono := mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hA0
    calc tail d (cellSet Y n) ((r : ℝ) + bd)
        ≤ C₁ * ((shellMax Y n r : ℝ) * (Fm - Fp) + R) := hbase'
      _ ≤ max C₀ C₁ * ((shellMax Y n r : ℝ) * (Fm - Fp) + R) := hmono
      _ = max C₀ C₁ * (shellMax Y n r : ℝ) * (Fm - Fp) + max C₀ C₁ * R := by ring
  have henv' : ∀ y : Site d, (localTime Y n y : ℝ) ≤
      Cm * max (binr - euclidNorm y) 0 + Cm * (N * Q ^ ((1 : ℝ) / d)) := by
    intro y
    calc (localTime Y n y : ℝ) ≤ Cm * max (binr - euclidNorm y) 0 +
          Cm * N * Q ^ ((1 : ℝ) / d) := henv y
      _ = Cm * max (binr - euclidNorm y) 0 + Cm * (N * Q ^ ((1 : ℝ) / d)) := by ring
  have hEnvres : maxRadius Y n ≤ binr + Ce * (N * Q ^ ((1 : ℝ) / d)) * L :=
    hEnv X ω n binr hn_ne h0 hstep hvec' hint' hrad' hM' hbge hble hvol henv'
  have hba' : |binr / N - a| ≤ max Cm Ce * Q :=
    le_trans hba (mul_le_mul_of_nonneg_right (le_max_left Cm Ce) hQnonneg)
  have hWnn : 0 ≤ N * Q ^ ((1 : ℝ) / d) :=
    mul_nonneg hNpos.le (Real.rpow_nonneg hQnonneg _)
  have hHres : maxRadius Y n ≤ binr + max Cm Ce * (N * Q ^ ((1 : ℝ) / d)) * L := by
    have h2 : Ce * (N * Q ^ ((1 : ℝ) / d)) ≤ max Cm Ce * (N * Q ^ ((1 : ℝ) / d)) :=
      mul_le_mul_of_nonneg_right (le_max_right Cm Ce) hWnn
    have h3 : Ce * (N * Q ^ ((1 : ℝ) / d)) * L ≤
        max Cm Ce * (N * Q ^ ((1 : ℝ) / d)) * L :=
      mul_le_mul_of_nonneg_right h2 hLpos.le
    linarith [hEnvres, h3]
  exact hInc Y n binr hn_no hba' hHres

end CERW.Support.Main
