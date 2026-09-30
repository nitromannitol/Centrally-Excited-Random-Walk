import CERW.Support.LocalTime.KernelFacts
import CERW.Support.LocalTime.KernelPoisson
import CERW.Support.LocalTime.GradientBound
import CERW.Support.LocalTime.GradientAsymp
import CERW.Support.Coarse.LevelSets
import LatticeProb.Walk.SRWPos

/-!
# From the kernel asymptotics to the kernel facts

The two clauses of `eq:kernel-asymptotics`, as they appear in the cited input, imply every
property of the potential kernel used downstream. In the plane, `b` is the limit of the partial
sums `G_M(0) - G_M(x)`, with `b(x) = (2/π) log|x| + κ + O(|x|^{-2})`. For `d ≥ 3`, `b = -G` with
`G(x) = c_d |x|^{2-d} + O(|x|^{-d})` and `c_d = 2/((d - 2) ω_d)`.
-/

namespace CERW.Support.LocalTime

open Filter Topology LatticeProb CERW CERW.Support.Coarse

variable {d : ℕ}

/-- The area of the unit disc, `ω₂ = π`, in the form needed to identify the planar gradient
asymptotic with the library statement phrased through `Real.pi`. -/
private lemma unitBallVolume_two : unitBallVolume 2 = Real.pi := by
  rw [unitBallVolume, EuclideanSpace.volume_ball_fin_two]
  simp [ENNReal.toReal_ofReal Real.pi_pos.le]

/-- Growth from an interior bound and a logarithmic exterior bound: if `|b|` is at most `K` on
`|x| ≤ R` and at most `A + B log|x|` on `R ≤ |x|`, with `R ≥ 1` and `K, A, B ≥ 0`, then
`|b|` is at most a constant times `log(|x| + 2)`. -/
private lemma exists_abs_le_mul_log_of_bounds {b : Site d → ℝ} {R K A B : ℝ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : ∀ x : Site d, euclidNorm x ≤ R → |b x| ≤ K)
    (hlarge : ∀ x : Site d, R ≤ euclidNorm x → |b x| ≤ A + B * Real.log (euclidNorm x)) :
    ∃ C : ℝ, ∀ x : Site d, |b x| ≤ C * Real.log (euclidNorm x + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(K + A) / Real.log 2 + B, fun x => ?_⟩
  set L : ℝ := Real.log (euclidNorm x + 2) with hLdef
  have hLge : Real.log 2 ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by norm_num) (by linarith [euclidNorm_nonneg x])
  have hL0 : 0 ≤ L := le_trans hlog2.le hLge
  have hone : 1 ≤ L / Real.log 2 := (one_le_div hlog2).mpr hLge
  have hkey : ∀ Z : ℝ, 0 ≤ Z → Z ≤ Z / Real.log 2 * L := by
    intro Z hZ
    calc Z = Z * 1 := (mul_one Z).symm
      _ ≤ Z * (L / Real.log 2) := mul_le_mul_of_nonneg_left hone hZ
      _ = Z / Real.log 2 * L := by ring
  have hKmono : K / Real.log 2 ≤ (K + A) / Real.log 2 + B := by
    have h1 : K / Real.log 2 ≤ (K + A) / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hlog2.le
    linarith
  have hAmono : A / Real.log 2 + B ≤ (K + A) / Real.log 2 + B := by
    have h1 : A / Real.log 2 ≤ (K + A) / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hlog2.le
    linarith
  by_cases hxR : euclidNorm x ≤ R
  · calc |b x| ≤ K := hsmall x hxR
      _ ≤ K / Real.log 2 * L := hkey K hK
      _ ≤ ((K + A) / Real.log 2 + B) * L := mul_le_mul_of_nonneg_right hKmono hL0
  · have hxR' : R ≤ euclidNorm x := le_of_lt (lt_of_not_ge hxR)
    have hlogmono : Real.log (euclidNorm x) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log (by linarith [hR, hxR']) (by linarith)
    calc |b x| ≤ A + B * Real.log (euclidNorm x) := hlarge x hxR'
      _ ≤ A + B * L := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogmono hB)
      _ ≤ A / Real.log 2 * L + B * L := by linarith [hkey A hA]
      _ = (A / Real.log 2 + B) * L := by ring
      _ ≤ ((K + A) / Real.log 2 + B) * L := mul_le_mul_of_nonneg_right hAmono hL0

/-- The planar kernel facts, with the radial profile `h_2(r) = (2/π) log r + κ`. -/
theorem kernelFacts_two {b : Site 2 → ℝ}
    (hlim : ∀ x, Tendsto (fun M : ℕ => srwGreen 2 M 0 - srwGreen 2 M x) atTop (𝓝 (b x)))
    {κ Cb Rb : ℝ} (hRb : 1 ≤ Rb)
    (hasymp : ∀ x, Rb ≤ euclidNorm x →
      |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ Cb * euclidNorm x ^ (-2 : ℝ)) :
    KernelFacts 2 b (fun r => 2 / Real.pi * Real.log r + κ) := by
  refine ⟨(fun x => walkOp_sub_self_of_tendsto (by norm_num) hlim x),
    exists_levelsets_two hRb hasymp, ?_, ?_, ?_⟩
  · obtain ⟨C, R, hC⟩ := exists_norm_centralDiff_sub_le_two hasymp
    refine ⟨max R 1, C, le_max_right _ _, fun x hx => ?_⟩
    have hxR : R ≤ euclidNorm x := le_trans (le_max_left _ _) hx
    simpa [unitBallVolume_two] using hC x hxR
  · obtain ⟨C, _hCpos, hC⟩ := exists_abs_add_sub_le_of_tendsto (d := 2) (by norm_num)
    refine ⟨C, fun x e he => ?_⟩
    simpa using hC b hlim x e he
  · have hlarge : ∀ x : Site 2, Rb ≤ euclidNorm x →
        |b x| ≤ (max Cb 0 + |κ|) + (2 / Real.pi) * Real.log (euclidNorm x) := by
      intro x hx
      have hbd := hasymp x hx
      have hx1 : 1 ≤ euclidNorm x := le_trans hRb hx
      have hrpow0 : 0 ≤ euclidNorm x ^ (-2 : ℝ) := Real.rpow_nonneg (euclidNorm_nonneg x) _
      have hrpow1 : euclidNorm x ^ (-2 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
      have hCb : Cb * euclidNorm x ^ (-2 : ℝ) ≤ max Cb 0 := by
        calc Cb * euclidNorm x ^ (-2 : ℝ) ≤ max Cb 0 * euclidNorm x ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_right (le_max_left Cb 0) hrpow0
          _ ≤ max Cb 0 * 1 := mul_le_mul_of_nonneg_left hrpow1 (le_max_right Cb 0)
          _ = max Cb 0 := mul_one _
      have hlog0 : 0 ≤ Real.log (euclidNorm x) := Real.log_nonneg hx1
      have hkappa : |2 / Real.pi * Real.log (euclidNorm x) + κ| ≤
          (2 / Real.pi) * Real.log (euclidNorm x) + |κ| := by
        calc |2 / Real.pi * Real.log (euclidNorm x) + κ|
            ≤ |2 / Real.pi * Real.log (euclidNorm x)| + |κ| := abs_add_le _ _
          _ = (2 / Real.pi) * Real.log (euclidNorm x) + |κ| := by
              rw [abs_of_nonneg (mul_nonneg (by positivity) hlog0)]
      have htri : |b x| ≤ |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| +
          |2 / Real.pi * Real.log (euclidNorm x) + κ| :=
        calc |b x| = |(b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)) +
              (2 / Real.pi * Real.log (euclidNorm x) + κ)| := by rw [sub_add_cancel]
          _ ≤ |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| +
              |2 / Real.pi * Real.log (euclidNorm x) + κ| :=
            abs_add_le (b x - (2 / Real.pi * Real.log (euclidNorm x) + κ))
              (2 / Real.pi * Real.log (euclidNorm x) + κ)
      linarith
    have hsmall : ∀ x : Site 2, euclidNorm x ≤ Rb →
        |b x| ≤ ∑ z ∈ ballFinset 2 Rb, |b z| := by
      intro x hx
      exact Finset.single_le_sum (f := fun z : Site 2 => |b z|)
        (fun z _ => abs_nonneg (b z)) (mem_ballFinset_iff.mpr hx)
    obtain ⟨C, hC⟩ := exists_abs_le_mul_log_of_bounds (d := 2) hRb
      (Finset.sum_nonneg (fun z _ => abs_nonneg (b z)))
      (by positivity : 0 ≤ max Cb 0 + |κ|) (by positivity : 0 ≤ 2 / Real.pi) hsmall hlarge
    exact ⟨C, hC⟩

/-- The kernel facts for `d ≥ 3`, with `b = -G` and the radial profile `h_d(r) = -c_d r^{2-d}`. -/
theorem kernelFacts_ge_three (hd : 3 ≤ d) {CG RG : ℝ} (hRG : 1 ≤ RG)
    (hasymp : ∀ x, RG ≤ euclidNorm x →
      |srwGreenInf d x - 2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ))| ≤
        CG * euclidNorm x ^ (-(d : ℝ))) :
    KernelFacts d (fun x => -srwGreenInf d x)
      (fun r => -(2 / (((d : ℝ) - 2) * unitBallVolume d) * r ^ (2 - (d : ℝ)))) := by
  have hcpos : 0 < 2 / (((d : ℝ) - 2) * unitBallVolume d) := by
    have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by
      have h2 : (2 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 2 < d)
      linarith
    exact div_pos (by norm_num) (mul_pos hd2 (unitBallVolume_pos d))
  have hGpos : ∀ x : Site d, 0 < srwGreenInf d x := by
    intro x
    have hsum := summable_srwHeat hd x
    have hsp : 0 < srwHeat d (graphNorm x) x :=
      srwHeat_pos (by omega : 1 ≤ d) (le_refl (graphNorm x)) rfl
    have hle := hsum.le_tsum (graphNorm x) (fun j _ => srwHeat_nonneg j x)
    change 0 < ∑' j : ℕ, srwHeat d j x
    exact lt_of_lt_of_le hsp hle
  refine ⟨(fun x => walkOp_neg_srwGreenInf_sub hd x), ?_, ?_, ?_, ?_⟩
  · exact exists_levelsets hd hRG hGpos hasymp
  · obtain ⟨C, R, hC⟩ := exists_norm_centralDiff_sub_le (G := srwGreenInf d) hd hasymp
    exact ⟨max R 1, C, le_max_right _ _, fun x hx => hC x (le_trans (le_max_left _ _) hx)⟩
  · obtain ⟨Cg, _hCgpos, hCg⟩ := exists_abs_srwGreenInf_add_sub_le hd
    refine ⟨Cg, fun x e he => ?_⟩
    have key : (fun y => -srwGreenInf d y) (x + e) - (fun y => -srwGreenInf d y) x
        = -(srwGreenInf d (x + e) - srwGreenInf d x) := by ring
    rw [key, abs_neg]
    exact hCg x e he
  · have hbabs : ∀ x : Site d, |(fun y => -srwGreenInf d y) x| = srwGreenInf d x := by
      intro x
      rw [abs_neg, abs_of_nonneg (srwGreenInf_nonneg x)]
    have hK0 : 0 ≤ ∑ z ∈ ballFinset d RG, srwGreenInf d z :=
      Finset.sum_nonneg (fun z _ => srwGreenInf_nonneg z)
    have hA0 : 0 ≤ 2 / (((d : ℝ) - 2) * unitBallVolume d) + max CG 0 :=
      add_nonneg hcpos.le (le_max_right CG 0)
    have hsmall : ∀ x : Site d, euclidNorm x ≤ RG →
        |(fun y => -srwGreenInf d y) x| ≤ ∑ z ∈ ballFinset d RG, srwGreenInf d z := by
      intro x hx
      rw [hbabs x]
      exact Finset.single_le_sum (f := fun z => srwGreenInf d z)
        (fun z _ => srwGreenInf_nonneg z) (mem_ballFinset_iff.mpr hx)
    have hlarge : ∀ x : Site d, RG ≤ euclidNorm x →
        |(fun y => -srwGreenInf d y) x| ≤
          (2 / (((d : ℝ) - 2) * unitBallVolume d) + max CG 0) +
            0 * Real.log (euclidNorm x) := by
      intro x hx
      rw [hbabs x, zero_mul, add_zero]
      have hx1 : 1 ≤ euclidNorm x := le_trans hRG hx
      have hbd := hasymp x hx
      have hpow1 : euclidNorm x ^ (2 - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 (by
          have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
          linarith)
      have hpow2 : euclidNorm x ^ (-(d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 (by
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith)
      have hupper : srwGreenInf d x ≤
          2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ)) +
            CG * euclidNorm x ^ (-(d : ℝ)) := by
        have h2 := (abs_le.mp hbd).2
        linarith
      have hCG : CG * euclidNorm x ^ (-(d : ℝ)) ≤ max CG 0 := by
        have hr0 : 0 ≤ euclidNorm x ^ (-(d : ℝ)) := Real.rpow_nonneg (euclidNorm_nonneg x) _
        calc CG * euclidNorm x ^ (-(d : ℝ)) ≤ max CG 0 * euclidNorm x ^ (-(d : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left CG 0) hr0
          _ ≤ max CG 0 * 1 := mul_le_mul_of_nonneg_left hpow2 (le_max_right CG 0)
          _ = max CG 0 := mul_one _
      have hc1 : 2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ)) ≤
          2 / (((d : ℝ) - 2) * unitBallVolume d) := by
        calc 2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ))
            ≤ 2 / (((d : ℝ) - 2) * unitBallVolume d) * 1 :=
              mul_le_mul_of_nonneg_left hpow1 hcpos.le
          _ = 2 / (((d : ℝ) - 2) * unitBallVolume d) := mul_one _
      linarith
    obtain ⟨Cb, hCb⟩ := exists_abs_le_mul_log_of_bounds (d := d) hRG hK0 hA0
      (le_refl (0 : ℝ)) hsmall hlarge
    exact ⟨Cb, hCb⟩

end CERW.Support.LocalTime
