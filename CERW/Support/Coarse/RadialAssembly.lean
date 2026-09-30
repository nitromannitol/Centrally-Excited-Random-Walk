import CERW.Support.Coarse.RadialMart
import CERW.Support.Coarse.RadialSource
import CERW.Support.Coarse.TailLower
import CERW.Support.Coarse.ShellCount
import CERW.Support.LocalTime.KernelFacts
import CERW.Support.Law.ScaleArith

/-!
# The radial test lemma

`lem:radial`, assembled from the kernel facts. For every integer `r₀ ≤ r ≤ n`, the source
inequality of the radial test (`eq:radial-source`), the lower bound of its source sum by
`F(r + b_d)`, the shell count (`eq:shell-count`) and the radial martingale bound
(`eq:radialmart`) combine into
`F(r + b_d) ≤ C M_sh(r) [F(r - b_d) - F(r + b_d)] + C [√(M_n r^{1-d} F(r - b_d) L) + r^{1-d} L]`.
-/

universe u

namespace CERW.Support.Coarse

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.LocalTime

/-- The visits of the path to the shell `r - 2 < |x| ≤ r + 3` number at most `M_sh(r)` times
the number of shell sites in the departure range. -/
private lemma shell_visits_le {d : ℕ} (x : ℕ → Site d) (n r : ℕ) :
    ∑ j ∈ range n, (if (r : ℝ) - 2 < euclidNorm (x j) ∧ euclidNorm (x j) ≤ (r : ℝ) + 3
        then (1 : ℝ) else 0) ≤
      (shellMax x n r : ℝ) *
        (((departureRange x n).filter (fun z => |euclidNorm z - r| ≤ 3)).card : ℝ) := by
  classical
  rw [sum_range_eq_sum_localTime x n
    (fun z => if (r : ℝ) - 2 < euclidNorm z ∧ euclidNorm z ≤ (r : ℝ) + 3 then (1 : ℝ) else 0)]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hc : (r : ℝ) - 2 < euclidNorm z ∧ euclidNorm z ≤ (r : ℝ) + 3
  · have hz : |euclidNorm z - r| ≤ 3 := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hl : (localTime x n z : ℝ) ≤ (shellMax x n r : ℝ) :=
      Nat.cast_le.mpr (localTime_le_shellMax x n r hz)
    simpa [hc, hz] using hl
  · simp only [hc, if_false, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The ratio bound `a^{1-d} c^{d-1} ≤ 3^{d-1}` for `0 < a` and `0 ≤ c ≤ 3a`. -/
private lemma rpow_mul_rpow_le {d : ℕ} (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hac : c ≤ 3 * a) :
    a ^ (1 - (d : ℝ)) * c ^ ((d : ℝ) - 1) ≤ 3 ^ ((d : ℝ) - 1) := by
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : a ^ (1 - (d : ℝ)) = (a ^ ((d : ℝ) - 1))⁻¹ := by
    rw [← Real.rpow_neg ha.le]
    congr 1
    ring
  rw [h1, ← div_eq_inv_mul, ← Real.div_rpow hc ha.le]
  exact Real.rpow_le_rpow (div_nonneg hc ha.le) ((div_le_iff₀ ha).mpr hac) hd1

/-- A threshold `r₀ > 2 bd` past which every real `r ≥ r₀` satisfies the radius conditions. -/
private lemma exists_threshold (d bd : ℕ) (r₁ R Ca : ℝ) :
    ∃ r₀ : ℕ, 2 * bd < r₀ ∧ ∀ r : ℝ, (r₀ : ℝ) ≤ r →
      r₁ ≤ r ∧ R ≤ r + 3 ∧ Ca * unitBallVolume d ≤ r + 3 ∧ Real.sqrt d + 2 ≤ r ∧
        2 * (bd : ℝ) + 1 ≤ r := by
  refine ⟨⌈r₁⌉₊ + ⌈R⌉₊ + ⌈Ca * unitBallVolume d⌉₊ + ⌈Real.sqrt d⌉₊ + 2 * bd + 3,
    by omega, ?_⟩
  intro r hr
  push_cast at hr
  have h1 := Nat.le_ceil r₁
  have h2 := Nat.le_ceil R
  have h3 := Nat.le_ceil (Ca * unitBallVolume d)
  have h4 := Nat.le_ceil (Real.sqrt d)
  have n1 : (0 : ℝ) ≤ ⌈r₁⌉₊ := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ ⌈R⌉₊ := Nat.cast_nonneg _
  have n3 : (0 : ℝ) ≤ ⌈Ca * unitBallVolume d⌉₊ := Nat.cast_nonneg _
  have n4 : (0 : ℝ) ≤ ⌈Real.sqrt d⌉₊ := Nat.cast_nonneg _
  have n5 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The pathwise inequality of the radial test at one integer radius `r`: the source
inequality, the lower bound of the source sum by `F(r + b_d)`, the shell visit count and the
shell count combine, given the bound on the radial martingale. -/
private lemma radial_step {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ} {h R Ca Cg ε bd Cm C : ℝ}
    (r : ℕ) (hε : 0 < ε) (hbd : 3 + Real.sqrt d / 2 < bd) (hr : 2 * bd + 1 ≤ (r : ℝ))
    (hin : ∀ x, euclidNorm x ≤ (r : ℝ) - 1 → b x ≤ h)
    (hout : ∀ x, (r : ℝ) + 1 ≤ euclidNorm x → h ≤ b x)
    (hpois : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (hR : R ≤ r + 3) (hCa : Ca * unitBallVolume d ≤ r + 3)
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hW : |dynkin ε (fun z => max (b z - h) 0) X n ω| ≤
      Cm * (Real.sqrt ((maxLocalTime (X · ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ))
            * tail d (cellSet (X · ω) n) ((r : ℝ) - bd) * L)
          + (r : ℝ) ^ (1 - (d : ℝ)) * L))
    (hCA : 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ *
      ((1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) ≤ C)
    (hCB : 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ * Cm ≤ C) :
    tail d (cellSet (X · ω) n) ((r : ℝ) + bd)
      ≤ C * shellMax (X · ω) n r
            * (tail d (cellSet (X · ω) n) ((r : ℝ) - bd)
              - tail d (cellSet (X · ω) n) ((r : ℝ) + bd))
        + C * (Real.sqrt ((maxLocalTime (X · ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ))
                * tail d (cellSet (X · ω) n) ((r : ℝ) - bd) * L)
            + (r : ℝ) ^ (1 - (d : ℝ)) * L) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hω0 : 0 < unitBallVolume d := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hσ : 0 < (d : ℝ) * unitBallVolume d := mul_pos hdpos hω0
  have hsqrt0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hbd0 : 0 < bd := by linarith
  have hr2 : (2 : ℝ) ≤ r := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hrb : bd < (r : ℝ) := by linarith
  have hsrc := radial_source (d := d) hd1 hr2 hε.le hin hout hpois hgradA hgrad hR hCa X ω h0 n
  have htail := tail_le_sum_rpow hd1 (fun j => X j ω) n hbd (by linarith : Real.sqrt d ≤ r)
  have hvis := shell_visits_le (fun j => X j ω) n r
  have hcard := card_shell_le hd1 (fun j => X j ω) n hbd hrb
  set T₁ := tail d (cellSet (X · ω) n) ((r : ℝ) + bd) with hT₁
  set T₂ := tail d (cellSet (X · ω) n) ((r : ℝ) - bd) with hT₂
  set M : ℝ := (shellMax (X · ω) n r : ℝ) with hM
  set S : ℝ := Real.sqrt ((maxLocalTime (X · ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) * T₂ * L)
    + (r : ℝ) ^ (1 - (d : ℝ)) * L with hS
  set s : ℝ := ∑ z ∈ (departureRange (X · ω) n).filter (fun z => (r : ℝ) + 3 < euclidNorm z),
    euclidNorm z ^ (1 - (d : ℝ)) with hs
  set N : ℝ := ∑ j ∈ range n, (if (r : ℝ) - 2 < euclidNorm (X j ω) ∧
    euclidNorm (X j ω) ≤ (r : ℝ) + 3 then (1 : ℝ) else 0) with hN
  set W : ℝ := |dynkin ε (fun z => max (b z - h) 0) X n ω| with hW'
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hS0 : 0 ≤ S := add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hrpos.le _) hL)
  have hQ : 0 < (d : ℝ) * unitBallVolume d * ((r : ℝ) + bd) ^ ((d : ℝ) - 1) :=
    mul_pos hσ (Real.rpow_pos_of_pos (by linarith) _)
  have hΔ : 0 ≤ T₂ - T₁ := by
    have h1 : 0 ≤ (d : ℝ) * unitBallVolume d * ((r : ℝ) + bd) ^ ((d : ℝ) - 1) * (T₂ - T₁) :=
      (Nat.cast_nonneg _).trans hcard
    exact (mul_nonneg_iff_of_pos_left hQ).mp h1
  have hMΔ : 0 ≤ M * (T₂ - T₁) := mul_nonneg hM0 hΔ
  have hK0 : 0 ≤ (1 + ε * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) :=
    mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (Real.rpow_nonneg (by linarith) _)
  have hKle : (1 + ε * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) ≤
      (1 + ε * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self Cg) (by positivity))
      (Real.rpow_nonneg (by linarith) _)
  have hrat := rpow_mul_rpow_le hd1 (a := (r : ℝ) - 1) (c := (r : ℝ) + bd) (by linarith)
    (by linarith) (by linarith)
  have hkey : (1 + ε * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N ≤
      (1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
        (M * (T₂ - T₁)) := by
    calc (1 + ε * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N
        ≤ (1 + ε * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N :=
          mul_le_mul_of_nonneg_right hKle hN0
      _ ≤ (1 + ε * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) *
            (M * (((departureRange (X · ω) n).filter
              (fun z => |euclidNorm z - r| ≤ 3)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hvis hK0
      _ ≤ (1 + ε * Real.sqrt d) * |Cg| * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) *
            (M * ((d : ℝ) * unitBallVolume d * ((r : ℝ) + bd) ^ ((d : ℝ) - 1) *
              (T₂ - T₁))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard hM0) hK0
      _ = (1 + ε * Real.sqrt d) * |Cg| * (d * unitBallVolume d) *
            (((r : ℝ) - 1) ^ (1 - (d : ℝ)) * ((r : ℝ) + bd) ^ ((d : ℝ) - 1)) *
              (M * (T₂ - T₁)) := by ring
      _ ≤ (1 + ε * Real.sqrt d) * |Cg| * (d * unitBallVolume d) * 3 ^ ((d : ℝ) - 1) *
            (M * (T₂ - T₁)) := by
          gcongr
      _ = (1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
            (M * (T₂ - T₁)) := by ring
  have hY : (1 + ε * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N + W ≤
      (1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
        (M * (T₂ - T₁)) + Cm * S := add_le_add hkey hW
  have hs' : s ≤ unitBallVolume d * ε⁻¹ *
      ((1 + ε * Real.sqrt d) * Cg * ((r : ℝ) - 1) ^ (1 - (d : ℝ)) * N + W) := by
    calc s = unitBallVolume d * ε⁻¹ * (ε * (unitBallVolume d)⁻¹ * s) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsrc (by positivity)
  have h2 : (0 : ℝ) ≤ 2 ^ ((d : ℝ) - 1) := by positivity
  have hmain : (d : ℝ) * unitBallVolume d * T₁ ≤ (d : ℝ) * unitBallVolume d *
      (2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ *
        ((1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
          (M * (T₂ - T₁)) + Cm * S)) := by
    calc (d : ℝ) * unitBallVolume d * T₁ ≤ 2 ^ ((d : ℝ) - 1) * s := htail
      _ ≤ 2 ^ ((d : ℝ) - 1) * (unitBallVolume d * ε⁻¹ *
            ((1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
              (M * (T₂ - T₁)) + Cm * S)) :=
          mul_le_mul_of_nonneg_left (hs'.trans (mul_le_mul_of_nonneg_left hY (by positivity)))
            h2
      _ = _ := by field_simp
  have hfin := le_of_mul_le_mul_left hmain hσ
  calc T₁ ≤ 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ *
        ((1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d) *
          (M * (T₂ - T₁)) + Cm * S) := hfin
    _ = 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ *
        ((1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) *
          (M * (T₂ - T₁)) + 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ * Cm * S := by ring
    _ ≤ C * (M * (T₂ - T₁)) + C * S :=
        add_le_add (mul_le_mul_of_nonneg_right hCA hMΔ) (mul_le_mul_of_nonneg_right hCB hS0)
    _ = C * M * (T₂ - T₁) + C * S := by ring

/-- `lem:radial`, for any kernel `b` with the kernel facts. -/
theorem radial_test_of_kernelFacts {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ} {h : ℝ → ℝ}
    (hK : KernelFacts d b h) :
    let bd : ℕ := ⌈Real.sqrt d / 2⌉₊ + 6
    ∃ r₀ : ℕ, 2 * bd < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ ∀ r : ℕ, r₀ ≤ r → r ≤ n →
            CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) + bd)
              ≤ C * CERW.shellMax (X · ω) n r
                  * (CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) - bd)
                    - CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) + bd))
                + C * (Real.sqrt ((CERW.maxLocalTime (X · ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ))
                        * CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) - bd) * L)
                    + (r : ℝ) ^ (1 - (d : ℝ)) * L)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro bd
  obtain ⟨r₁, hr₁⟩ := hK.levels
  obtain ⟨R, Ca, -, hgradA⟩ := hK.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨r₀, hr₀bd, hr₀⟩ := exists_threshold d bd r₁ R Ca
  have hbd : 3 + Real.sqrt d / 2 < (bd : ℝ) := by
    have := Nat.le_ceil (Real.sqrt d / 2)
    show _ < ((⌈Real.sqrt d / 2⌉₊ + 6 : ℕ) : ℝ)
    push_cast
    linarith
  refine ⟨r₀, hr₀bd, ?_⟩
  intro ε hε hεd p hp
  have hbdr₀ : (bd : ℝ) < r₀ := by exact_mod_cast (by omega : bd < r₀)
  obtain ⟨Cm, hCm0, hCm⟩ := exists_radial_mart.{u} hd hε.le hεd (b := b) (h := h) (Cg := Cg)
    (r₀ := (r₀ : ℝ)) (bd := (bd : ℝ)) (by linarith) hbdr₀ (hr₀ r₀ le_rfl).2.2.2.1
    (fun r hr x hx => ((hr₁ r (hr₀ r hr).1 x).1 hx)) hgrad hp
  have hω0 : 0 < unitBallVolume d := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set c₁ : ℝ := 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ *
    ((1 + ε * Real.sqrt d) * |Cg| * 3 ^ ((d : ℝ) - 1) * (d * unitBallVolume d)) with hc₁
  set c₂ : ℝ := 2 ^ ((d : ℝ) - 1) * (d * ε)⁻¹ * Cm with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨Cm + c₁ + c₂ + 1, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn L
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  refine measure_le_of_subset_union (fun ω hω => ?_) (hCm hX n hn) hX.start
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  by_contra hcon
  refine hω ?_
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hA', hN'⟩ := hcon
  have h0 : X 0 ω = 0 := by simpa using hN'
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hA'
  intro r hr₀r hrn
  have hthr := hr₀ (r : ℝ) (by exact_mod_cast hr₀r)
  exact radial_step hd r hε hbd hthr.2.2.2.2 (fun x hx => (hr₁ r hthr.1 x).1 hx)
    (fun x hx => (hr₁ r hthr.1 x).2 hx) hK.poisson hgradA hgrad hthr.2.1 hthr.2.2.1 X ω h0 n L
    hL0 (hA' r (by exact_mod_cast hr₀r) hrn) (by linarith) (by linarith)

end CERW.Support.Coarse
