import CERW.Support.Main.EventProb
import CERW.Support.Main.HausdorffGood
import CERW.Support.Main.HausdorffArith

/-!
# The Hausdorff bound from the kernel facts

`eq:hausdorff` with the two-sided planar remark. For each `p`, `exists_event_prob` bounds the
failure probability of `fluctEvent`. On `fluctEvent`, for large `n`, the deterministic core
`hcore` (the statement of `exists_good_of_event`) gives `fluctGood` and an unvisited site of
norm less than `aN + C N Q`. `hausdorff_of_good` turns `fluctGood` into the Hausdorff bound and
the planar inner inclusion. In the plane, `N Q = n^{1/6} √L` (`planar_inner_rate`).
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main

open CERW CERW.Support.LocalTime

/-- The outer rate factor of `eq:hausdorff` is nonnegative. -/
private lemma hausdorff_rate_nonneg (d n : ℕ) :
    0 ≤ (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * Real.log (n + 2) ^ ((5 : ℝ) / 4)
      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
        * Real.log (n + 2) ^ ((2 * d : ℝ) / (2 * d - 1))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : (0 : ℝ) ≤ Real.log (n + 2) := Real.log_nonneg (by linarith [hn])
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg hL _)
  · exact mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg hL _)

/-- `eq:hausdorff` with the two-sided planar remark, for any kernel `b` with the kernel facts,
given the deterministic core (`hcore`, the statement of `exists_good_of_event`). -/
theorem hausdorff_bound_of_core {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h)
    (hcore : ∀ ε : ℝ, 0 < ε → ∀ C₀ C₁ : ℝ, 0 < C₀ → 0 < C₁ → ∀ bd r₀ : ℕ, 1 ≤ bd →
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type u} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        let Q : ℝ :=
          if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
        fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
          fluctGood d ε C (fun j => X j ω) n ∧
          ∃ x : Site d, x ∉ CERW.departureRange (fun j => X j ω) n ∧
            euclidNorm x < a * N + C * N * Q) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ (Metric.hausdorffEDist
                    ((fun x => N⁻¹ • CERW.toSpace x) '' ↑(CERW.visitedRange (X · ω) n))
                    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
                  ≤ ENNReal.ofReal (C * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
                      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
                        * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
                    ∃ x : Site d, euclidNorm x < a * N + C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L ∧ x ∉ CERW.departureRange (X · ω) n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro ωd ε hε hεd a p hp
  obtain ⟨r₀, hr₀⟩ := exists_event_prob (d := d) hd hK
  obtain ⟨C₀, C₁, hC₀, hC₁, hprob⟩ := hr₀ ε hε hεd p hp
  obtain ⟨C, hCpos, n₀, hcore_prop⟩ :=
    hcore ε hε C₀ C₁ hC₀ hC₁ (⌈Real.sqrt d / 2⌉₊ + 6) r₀ (by omega)
  obtain ⟨C', n₁, hC'pos, hgood_prop⟩ := hausdorff_of_good (d := d) hd hε hCpos.le
  let Cfin : ℝ := max (max C C') C₁
  let Nfin : ℕ := max (max n₀ n₁) 2
  have hCle : C ≤ Cfin := by
    dsimp only [Cfin]
    exact le_trans (le_max_left C C') (le_max_left (max C C') C₁)
  have hC'le : C' ≤ Cfin := by
    dsimp only [Cfin]
    exact le_trans (le_max_right C C') (le_max_left (max C C') C₁)
  have hC₁le : C₁ ≤ Cfin := by
    dsimp only [Cfin]
    exact le_max_right (max C C') C₁
  refine ⟨Cfin, Nfin, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hCpos hCle
  · dsimp only [Nfin]
    omega
  · intro Ω _ μ _ X hX n hn
    dsimp only
    have hn₂ : 2 ≤ n := le_trans (le_max_right (max n₀ n₁) 2) hn
    have hn₀ : n₀ ≤ n :=
      le_trans (le_trans (le_max_left n₀ n₁) (le_max_left (max n₀ n₁) 2)) hn
    have hn₁ : n₁ ≤ n :=
      le_trans (le_trans (le_max_right n₀ n₁) (le_max_left (max n₀ n₁) 2)) hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hLpos : 0 < Real.log ((n : ℝ) + 2) :=
      Real.log_pos (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have hn16 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hsl : (0 : ℝ) ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) := Real.sqrt_nonneg _
    have hprob' := hprob μ X hX n hn₂
    refine le_trans ?_ (hprob'.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC₁le
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))))
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hf
    obtain ⟨hgood, x, hxnot, hxlt⟩ := hcore_prop X ω n hn₀ hf
    obtain ⟨hgdH, hgdI⟩ := hgood_prop (fun j => X j ω) n hn₁ hgood
    have hHaus := hgdH.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC'le (hausdorff_rate_nonneg d n)))
    refine hω ⟨hHaus, ?_⟩
    intro hd2
    have hNQ : (n : ℝ) ^ ((1 : ℝ) / (d + 1))
          * (if d = 2
              then (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
              else (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
                ^ ((d : ℝ) / (2 * d - 1)))
        = (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log ((n : ℝ) + 2)) := by
      rw [hd2]
      rw [if_pos rfl]
      convert planar_inner_rate (n := (n : ℝ)) (L := Real.log ((n : ℝ) + 2)) hnpos hLpos using 1
      norm_num
    have hxlt' : euclidNorm x < a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        + C * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log ((n : ℝ) + 2)) := by
      have hxlt'' : euclidNorm x < a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
          + C * (n : ℝ) ^ ((1 : ℝ) / (d + 1))
            * (if d = 2
                then (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
                  ^ ((1 : ℝ) / 2)
                else (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
                  ^ ((d : ℝ) / (2 * d - 1))) := hxlt
      rw [mul_assoc, hNQ] at hxlt''
      simpa only [mul_assoc] using hxlt''
    constructor
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      refine hgdI hd2 ?_
      simp only [Set.mem_setOf_eq]
      have hCs : C' * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log ((n : ℝ) + 2))
          ≤ Cfin * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC'le hn16) hsl
      exact lt_of_lt_of_le hy
        (sub_le_sub_left hCs (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))))
    · refine ⟨x, ?_, hxnot⟩
      have hCs : C * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log ((n : ℝ) + 2))
          ≤ Cfin * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hn16) hsl
      exact lt_of_lt_of_le hxlt' (by linarith only [hCs])

end CERW.Support.Main
