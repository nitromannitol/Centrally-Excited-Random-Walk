import CERW.Support.LocalTime.KernelFacts
import CERW.Support.LocalTime.DynkinLocal
import CERW.Support.LocalTime.SourceSum
import CERW.Support.Occupation.Facts

/-!
# The pointwise decomposition of the local time

`eq:pointwise`: on a path from the origin with unit steps, for every lattice target `|y| ≤ 3n`,
`ℓ_n(y) = U_{D_n}(y) + ρ_n(y) - 𝓜^y_n` with `|ρ_n(y)| ≤ C L`. The remainder
`ρ_n(y) = b(X_n - y) - b(-y) + [ε Σ_{x ∈ A_n} u_x · Db(x - y) - U_{D_n}(y)]` combines the endpoint
difference, which is `O(L)` by the growth of `b`, and the source-sum comparison, which is
`O(εL)`.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ}

/-- The Euclidean norm of a lattice difference is at most the sum of the two norms. -/
private lemma euclidNorm_sub_le (x y : Site d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  calc euclidNorm (x - y) = euclidNorm (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ euclidNorm x + euclidNorm (-y) := euclidNorm_add_le _ _
    _ = euclidNorm x + euclidNorm y := by rw [CERW.Generic.Lattice.euclidNorm_neg]

/-- A cell lies in the open ball of radius `R` when its site satisfies `|x| + √d/2 < R`. -/
private lemma cell_subset_ball_of_lt (x : Site d) {R : ℝ}
    (h : euclidNorm x + Real.sqrt d / 2 < R) : cell x ⊆ Metric.ball 0 R := by
  intro v hv
  rw [mem_ball_zero_iff]
  calc ‖v‖ ≤ ‖toSpace x‖ + ‖v - toSpace x‖ := norm_le_norm_add_norm_sub' v (toSpace x)
    _ = euclidNorm x + ‖v - toSpace x‖ := by rw [norm_toSpace]
    _ ≤ euclidNorm x + Real.sqrt d / 2 :=
        add_le_add le_rfl (norm_sub_toSpace_le_of_mem_cell hv)
    _ < R := h

/-- The logarithmic comparison constant `1 + log(4 + √d)/log 3` is nonnegative. -/
private lemma one_add_log_div_log_three_nonneg (d : ℕ) :
    0 ≤ 1 + Real.log (4 + Real.sqrt d) / Real.log 3 := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogd : 0 ≤ Real.log (4 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg d] : (1 : ℝ) ≤ 4 + Real.sqrt d)
  have := div_nonneg hlogd (le_of_lt hlog3pos)
  linarith

/-- For `n ≥ 1`, the logarithm of `4n + √d + 2` is at most the logarithmic comparison
constant times `log(n + 2)`. -/
private lemma log_four_mul_add_sqrt_add_two_le (d n : ℕ) (hn : 1 ≤ n) :
    Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsn : Real.sqrt d ≤ Real.sqrt d * n := by
    simpa using mul_le_mul_of_nonneg_left hn1 hs
  have hle1 : 4 * (n : ℝ) + Real.sqrt d + 2 ≤ (4 + Real.sqrt d) * ((n : ℝ) + 2) := by
    nlinarith [hs, hsn, hn1]
  have hpos1 : 0 < 4 * (n : ℝ) + Real.sqrt d + 2 := by linarith [hs, hn1]
  have hn2 : 0 < (n : ℝ) + 2 := by linarith [hn1]
  have h4 : 0 < 4 + Real.sqrt d := by linarith [hs]
  have hpos2 : 0 < (4 + Real.sqrt d) * ((n : ℝ) + 2) := mul_pos h4 hn2
  have hlog1 : Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
      Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) :=
    Real.log_le_log hpos1 hle1
  have hmul : Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) =
      Real.log (4 + Real.sqrt d) + Real.log ((n : ℝ) + 2) := by
    rw [Real.log_mul]
    · exact ne_of_gt h4
    · exact ne_of_gt hn2
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ Real.log ((n : ℝ) + 2) := by
    apply Real.log_le_log (by norm_num)
    have h3n : 3 ≤ n + 2 := by omega
    exact_mod_cast h3n
  have hlogd : 0 ≤ Real.log (4 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [hs] : (1 : ℝ) ≤ 4 + Real.sqrt d)
  have hratio : 1 ≤ Real.log ((n : ℝ) + 2) / Real.log 3 := by
    rw [le_div_iff₀ hlog3pos]
    linarith
  have hstep : Real.log (4 + Real.sqrt d) ≤
      (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
    calc Real.log (4 + Real.sqrt d) = Real.log (4 + Real.sqrt d) * 1 := by ring
      _ ≤ Real.log (4 + Real.sqrt d) * (Real.log ((n : ℝ) + 2) / Real.log 3) :=
          mul_le_mul_of_nonneg_left hratio hlogd
      _ = (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by ring
  calc Real.log (4 * (n : ℝ) + Real.sqrt d + 2)
      ≤ Real.log ((4 + Real.sqrt d) * ((n : ℝ) + 2)) := hlog1
    _ = Real.log (4 + Real.sqrt d) + Real.log ((n : ℝ) + 2) := hmul
    _ ≤ Real.log ((n : ℝ) + 2) +
        (Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by
        linarith [hstep]
    _ = (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2) := by ring

/-- `eq:pointwise`: `|ℓ_n(y) - U_{D_n}(y) + 𝓜^y_n| ≤ C log(n + 2)` for lattice `|y| ≤ 3n`, on every
path from the origin with `|X_j| ≤ j`. -/
theorem exists_abs_localTime_sub_potential_add_dynkin_le (hd : 2 ≤ d) {b : Site d → ℝ}
    {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω),
      X 0 ω = 0 → (∀ j, euclidNorm (X j ω) ≤ j) → ∀ n : ℕ, 1 ≤ n → ∀ y : Site d,
        euclidNorm y ≤ 3 * n →
          |(localTime (fun j => X j ω) n y : ℝ) -
              potential d ε (cellSet (fun j => X j ω) n) (toSpace y) +
              dynkin ε (fun z => b (z - y)) X n ω| ≤ C * Real.log (n + 2) := by
  obtain ⟨R, Ca, hR, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cb, hb⟩ := hK.growth
  obtain ⟨C_S, hCS, hsource⟩ := exists_abs_source_sum_sub_potential_le hd hR hgradA hgrad
  let Cb' : ℝ := max Cb 0
  let CS' : ℝ := max C_S 0
  let K : ℝ := 1 + Real.log (4 + Real.sqrt d) / Real.log 3
  refine ⟨(2 * Cb' + CS') * K, ?_, ?_⟩
  · have hb' : 0 ≤ Cb' := le_max_right Cb 0
    have hS' : 0 ≤ CS' := le_max_right C_S 0
    have hKnn : 0 ≤ K := by
      change 0 ≤ 1 + Real.log (4 + Real.sqrt d) / Real.log 3
      exact one_add_log_div_log_three_nonneg d
    exact mul_nonneg (by linarith) hKnn
  · intro ε hε0 hε1 Ω X ω h0 hpath n hn y hy
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
    let R' : ℝ := 4 * (n : ℝ) + Real.sqrt d
    set U : ℝ := potential d ε (cellSet (fun j => X j ω) n) (toSpace y) with hU
    rw [localTime_eq_dynkin hK.poisson ε X ω h0 n y]
    set S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n,
        inner ℝ (unitDir (toSpace x)) (centralDiff b (x - y)) with hS
    have hgoal_eq : (b (X n ω - y) - b (-y) + ε * S -
          dynkin ε (fun z => b (z - y)) X n ω) - U +
          dynkin ε (fun z => b (z - y)) X n ω =
        b (X n ω - y) - b (-y) + (ε * S - U) := by ring
    rw [hgoal_eq]
    have hR'1 : 1 ≤ R' := by
      change (1 : ℝ) ≤ 4 * (n : ℝ) + Real.sqrt d
      linarith
    have hsub : euclidNorm (X n ω - y) ≤ 4 * (n : ℝ) := by
      calc euclidNorm (X n ω - y) ≤ euclidNorm (X n ω) + euclidNorm y := euclidNorm_sub_le _ _
        _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add (hpath n) hy
        _ = 4 * (n : ℝ) := by ring
    have hlogX : Real.log (euclidNorm (X n ω - y) + 2) ≤ Real.log (R' + 2) := by
      apply Real.log_le_log
      · linarith [euclidNorm_nonneg (X n ω - y)]
      · change euclidNorm (X n ω - y) + 2 ≤ 4 * (n : ℝ) + Real.sqrt d + 2
        linarith
    have hlogY : Real.log (euclidNorm (-y) + 2) ≤ Real.log (R' + 2) := by
      rw [CERW.Generic.Lattice.euclidNorm_neg]
      apply Real.log_le_log
      · linarith [euclidNorm_nonneg y]
      · change euclidNorm y + 2 ≤ 4 * (n : ℝ) + Real.sqrt d + 2
        linarith
    have hb1 : |b (X n ω - y)| ≤ Cb' * Real.log (R' + 2) := by
      have h1 : |b (X n ω - y)| ≤ Cb * Real.log (euclidNorm (X n ω - y) + 2) := hb _
      have h2 : Cb * Real.log (euclidNorm (X n ω - y) + 2) ≤
          Cb' * Real.log (euclidNorm (X n ω - y) + 2) :=
        mul_le_mul_of_nonneg_right (le_max_left Cb 0)
          (Real.log_nonneg (by linarith [euclidNorm_nonneg (X n ω - y)]))
      have h3 : Cb' * Real.log (euclidNorm (X n ω - y) + 2) ≤
          Cb' * Real.log (R' + 2) :=
        mul_le_mul_of_nonneg_left hlogX (le_max_right Cb 0)
      linarith
    have hb2 : |b (-y)| ≤ Cb' * Real.log (R' + 2) := by
      have h1 : |b (-y)| ≤ Cb * Real.log (euclidNorm (-y) + 2) := hb _
      have h2 : Cb * Real.log (euclidNorm (-y) + 2) ≤
          Cb' * Real.log (euclidNorm (-y) + 2) :=
        mul_le_mul_of_nonneg_right (le_max_left Cb 0)
          (Real.log_nonneg (by
            rw [CERW.Generic.Lattice.euclidNorm_neg]
            linarith [euclidNorm_nonneg y]))
      have h3 : Cb' * Real.log (euclidNorm (-y) + 2) ≤ Cb' * Real.log (R' + 2) :=
        mul_le_mul_of_nonneg_left hlogY (le_max_right Cb 0)
      linarith
    have hcell : ∀ x ∈ departureRange (fun j => X j ω) n,
        euclidNorm (x - y) ≤ R' ∧ cell x ⊆ Metric.ball 0 R' := by
      intro x hx
      rw [departureRange] at hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hjn : (j : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
      have hxnorm : euclidNorm (X j ω) ≤ (n : ℝ) := (hpath j).trans hjn
      refine ⟨?_, ?_⟩
      · calc euclidNorm (X j ω - y)
            ≤ euclidNorm (X j ω) + euclidNorm y := euclidNorm_sub_le _ _
          _ ≤ (n : ℝ) + 3 * (n : ℝ) := add_le_add hxnorm hy
          _ = 4 * (n : ℝ) := by ring
          _ ≤ R' := by
              change 4 * (n : ℝ) ≤ 4 * (n : ℝ) + Real.sqrt d
              linarith
      · apply cell_subset_ball_of_lt
        change euclidNorm (X j ω) + Real.sqrt d / 2 < 4 * (n : ℝ) + Real.sqrt d
        nlinarith [hxnorm, hn1, hs]
    have hyR' : euclidNorm y ≤ 2 * R' := by
      change euclidNorm y ≤ 2 * (4 * (n : ℝ) + Real.sqrt d)
      linarith
    have hsrc_raw := hsource ε hε0 (fun j => X j ω) n y R' hR'1 hyR' hcell
    have hsrc : |ε * S - U| ≤ C_S * ε * Real.log (R' + 2) := by
      rw [← hS, ← hU] at hsrc_raw
      exact hsrc_raw
    have hlogR' : 0 ≤ Real.log (R' + 2) := by
      apply Real.log_nonneg
      change (1 : ℝ) ≤ 4 * (n : ℝ) + Real.sqrt d + 2
      linarith
    have hsrc' : |ε * S - U| ≤ CS' * Real.log (R' + 2) := by
      have h1 : C_S * ε * Real.log (R' + 2) ≤ C_S * Real.log (R' + 2) := by
        have hε : C_S * ε ≤ C_S := by
          simpa using mul_le_mul_of_nonneg_left hε1 hCS
        exact mul_le_mul_of_nonneg_right hε hlogR'
      have h2 : C_S * Real.log (R' + 2) ≤ CS' * Real.log (R' + 2) :=
        mul_le_mul_of_nonneg_right (le_max_left C_S 0) hlogR'
      linarith
    have hcomb : |b (X n ω - y) - b (-y) + (ε * S - U)| ≤
        (Cb' + Cb' + CS') * Real.log (R' + 2) := by
      have htri : |b (X n ω - y) - b (-y) + (ε * S - U)| ≤
          |b (X n ω - y)| + |b (-y)| + |ε * S - U| := by
        have h1 : |b (X n ω - y) - b (-y) + (ε * S - U)| ≤
            |b (X n ω - y) - b (-y)| + |ε * S - U| := abs_add_le _ _
        have h2 : |b (X n ω - y) - b (-y)| ≤ |b (X n ω - y)| + |b (-y)| := by
          rw [sub_eq_add_neg]
          calc |b (X n ω - y) + -b (-y)| ≤ |b (X n ω - y)| + |-b (-y)| := abs_add_le _ _
            _ = |b (X n ω - y)| + |b (-y)| := by rw [abs_neg]
        linarith
      calc |b (X n ω - y) - b (-y) + (ε * S - U)|
          ≤ |b (X n ω - y)| + |b (-y)| + |ε * S - U| := htri
        _ ≤ Cb' * Real.log (R' + 2) + Cb' * Real.log (R' + 2) + CS' * Real.log (R' + 2) :=
            add_le_add (add_le_add hb1 hb2) hsrc'
        _ = (Cb' + Cb' + CS') * Real.log (R' + 2) := by ring
    have hfinal : (Cb' + Cb' + CS') * Real.log (R' + 2) ≤
        (2 * Cb' + CS') * K * Real.log ((n : ℝ) + 2) := by
      have hlogK : Real.log (R' + 2) ≤ K * Real.log ((n : ℝ) + 2) := by
        change Real.log (4 * (n : ℝ) + Real.sqrt d + 2) ≤
          (1 + Real.log (4 + Real.sqrt d) / Real.log 3) * Real.log ((n : ℝ) + 2)
        exact log_four_mul_add_sqrt_add_two_le d n hn
      have hcoef : 0 ≤ Cb' + Cb' + CS' := by
        have h1 : 0 ≤ Cb' := le_max_right Cb 0
        have h2 : 0 ≤ CS' := le_max_right C_S 0
        linarith
      calc (Cb' + Cb' + CS') * Real.log (R' + 2)
          ≤ (Cb' + Cb' + CS') * (K * Real.log ((n : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left hlogK hcoef
        _ = (2 * Cb' + CS') * K * Real.log ((n : ℝ) + 2) := by ring
    calc |b (X n ω - y) - b (-y) + (ε * S - U)|
        ≤ (Cb' + Cb' + CS') * Real.log (R' + 2) := hcomb
      _ ≤ (2 * Cb' + CS') * K * Real.log ((n : ℝ) + 2) := hfinal

end CERW.Support.LocalTime
