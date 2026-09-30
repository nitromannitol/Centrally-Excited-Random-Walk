import CERW.Support.Main.Event
import CERW.Support.Coarse.Assembly
import CERW.Support.Coarse.RadialAssembly
import CERW.Support.LocalTime.LocalAssembly
import CERW.Support.LocalTime.Pointwise
import CERW.Support.LocalTime.LocalMart
import CERW.Support.Contact.QuadraticError

/-!
# The probability of the event

For every `p > 0`, the event `fluctEvent` fails with probability at most `C n^{-p}`. Its parts
come from `prop:coarse` (`coarse_bounds_of_kernelFacts`), `lem:local`
(`local_time_potential_of_kernelFacts`), `eq:localmart` (`exists_local_mart`), the quadratic
error (`exists_quadratic_error`, with `K` the constant of `prop:coarse`), `eq:vector`
(`exists_compensated_bound`) and `lem:radial` (`radial_test_of_kernelFacts`). The path clause and
`eq:pointwise` (`exists_abs_localTime_sub_potential_add_dynkin_le`) hold almost surely. Take a
union bound over the seven exceptional events.
-/

universe u

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW CERW.Support.LocalTime

variable {d : ℕ}

/-- The logarithm `log (n + 2)` is nonnegative. -/
private lemma log_add_two_nonneg {n : ℕ} : 0 ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_nonneg (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- The scale `λ_n` of `eq:M` is nonnegative once `L ≥ 0`. -/
private lemma lam_nonneg {L : ℝ} (hL : 0 ≤ L) (d : ℕ) : 0 ≤ (if d = 2 then L ^ 2 else L) := by
  split_ifs
  · exact sq_nonneg L
  · exact hL

/-- The error scale `e_n(m)` of `eq:approx` is nonnegative once `L ≥ 0`. -/
private lemma error_scale_nonneg {L m : ℝ} (hL : 0 ≤ L) (d : ℕ) :
    0 ≤ (if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L) := by
  split_ifs
  · exact add_nonneg (mul_nonneg (Real.sqrt_nonneg m) hL) hL
  · exact add_nonneg (Real.sqrt_nonneg _) hL

/-- A bound with constant `C` holds with any larger constant when the bounding quantity is
nonnegative. -/
private lemma le_mul_of_le_of_le {x C C₁ A : ℝ} (hC : C ≤ C₁) (hA : 0 ≤ A) (h : x ≤ C * A) :
    x ≤ C₁ * A :=
  h.trans (mul_le_mul_of_nonneg_right hC hA)

/-- The radial inequality with constant `C` holds with any larger constant, when the shell
maximum `S`, the tail difference `D` and the error term `A` are nonnegative. -/
private lemma radial_le_of_le {F C C₁ S D A : ℝ} (hC : C ≤ C₁) (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (h : F ≤ C * S * D + C * A) : F ≤ C₁ * S * D + C₁ * A := by
  have h1 : C * S * D ≤ C₁ * S * D :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hS) hD
  have h2 : C * A ≤ C₁ * A := mul_le_mul_of_nonneg_right hC hA
  linarith only [h, h1, h2]

/-- A measure bound for a set covered by six sets of small measure and a null set. -/
private lemma measure_le_of_subset_union_six {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A₁ A₂ A₃ A₄ A₅ A₆ N B : Set Ω} {a₁ a₂ a₃ a₄ a₅ a₆ c : ENNReal}
    (hsub : B ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆ ∪ N) (h₁ : μ A₁ ≤ a₁) (h₂ : μ A₂ ≤ a₂)
    (h₃ : μ A₃ ≤ a₃) (h₄ : μ A₄ ≤ a₄) (h₅ : μ A₅ ≤ a₅) (h₆ : μ A₆ ≤ a₆) (hN : μ N = 0)
    (hc : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ≤ c) : μ B ≤ c := by
  refine (measure_mono hsub).trans ((measure_union_le _ N).trans ?_)
  rw [hN, add_zero]
  refine le_trans ?_ hc
  refine (measure_union_le _ A₆).trans (add_le_add ?_ h₆)
  refine (measure_union_le _ A₅).trans (add_le_add ?_ h₅)
  refine (measure_union_le _ A₄).trans (add_le_add ?_ h₄)
  refine (measure_union_le _ A₃).trans (add_le_add ?_ h₃)
  exact (measure_union_le A₁ A₂).trans (add_le_add h₁ h₂)

/-- Six terms `ofReal (aᵢ t)` with nonnegative `aᵢ` and `t` add up to at most `ofReal (C t)` when
`∑ aᵢ ≤ C`. -/
private lemma ofReal_six_le {a₁ a₂ a₃ a₄ a₅ a₆ C t : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂)
    (h₃ : 0 ≤ a₃) (h₄ : 0 ≤ a₄) (h₅ : 0 ≤ a₅) (h₆ : 0 ≤ a₆) (ht : 0 ≤ t)
    (hC : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ≤ C) :
    ENNReal.ofReal (a₁ * t) + ENNReal.ofReal (a₂ * t) + ENNReal.ofReal (a₃ * t) +
      ENNReal.ofReal (a₄ * t) + ENNReal.ofReal (a₅ * t) + ENNReal.ofReal (a₆ * t) ≤
      ENNReal.ofReal (C * t) := by
  have b₁ := mul_nonneg h₁ ht
  have b₂ := mul_nonneg h₂ ht
  have b₃ := mul_nonneg h₃ ht
  have b₄ := mul_nonneg h₄ ht
  have b₅ := mul_nonneg h₅ ht
  have b₆ := mul_nonneg h₆ ht
  rw [← ENNReal.ofReal_add b₁ b₂, ← ENNReal.ofReal_add (add_nonneg b₁ b₂) b₃,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg b₁ b₂) b₃) b₄,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg b₁ b₂) b₃) b₄) b₅,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg (add_nonneg b₁ b₂) b₃) b₄) b₅) b₆]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_le_mul_of_nonneg_right hC ht
  linarith only [this]

/-- For every `p > 0`, the event of the fluctuation theorem's proof fails with probability at
most `C₁ n^{-p}`, with the radial parameters of `lem:radial`. -/
theorem exists_event_prob (hd : 2 ≤ d) {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h) :
    let bd : ℕ := ⌈Real.sqrt d / 2⌉₊ + 6
    ∃ r₀ : ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ fluctEvent d ε b C₀ C₁ bd r₀ X ω n} ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-p)) := by
  intro bd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨r₀, hr₀, hrad⟩ := Coarse.radial_test_of_kernelFacts.{u} hd hK
  refine ⟨r₀, ?_⟩
  intro ε hε hεd p hp
  obtain ⟨c, C₀, -, hC₀, hcoarse⟩ := Coarse.coarse_bounds_of_kernelFacts.{u} hd hK ε hε hεd p hp
  obtain ⟨Cd, hCd, hloc⟩ := local_time_potential_of_kernelFacts.{u} hd hK
  obtain ⟨Cl, hCl, hloc'⟩ := hloc ε hε hεd p hp
  obtain ⟨Cr, hCr, hrad'⟩ := hrad ε hε hεd p hp
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cm, hCm, hmart⟩ := exists_local_mart.{u} hd hε.le hεd hgrad hp
  obtain ⟨Cq, hCq, hquad⟩ := Contact.exists_quadratic_error.{u} hd hε.le hεd hC₀ hp
  obtain ⟨Cv, hCv, hvec⟩ := Coarse.exists_compensated_bound.{u} hd1 hε.le hεd hp
  obtain ⟨Cp, hCp, hpt⟩ := exists_abs_localTime_sub_potential_add_dynkin_le.{u} hd hK
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = C₀ + Cd + Cl + Cm + Cq + Cv + Cr + Cp := ⟨_, rfl⟩
  have hC₁pos : 0 < C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCd₁ : Cd ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCl₁ : Cl ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCm₁ : Cm ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCq₁ : Cq ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCv₁ : Cv ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCr₁ : Cr ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hCp₁ : Cp ≤ C₁ := by linarith only [hC₁, hC₀, hCd, hCl, hCm, hCq, hCv, hCr, hCp]
  have hsum : C₀ + Cl + Cm + Cq + Cv + Cr ≤ C₁ := by
    linarith only [hC₁, hCd, hCp]
  refine ⟨C₀, C₁, hC₀, hC₁pos, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 := by
    refine ae_iff.mp ?_
    filter_upwards [ae_iff.mpr hX.start, ae_all_iff.mpr
      (fun j => CERW.Support.Law.ae_sub_mem_unitSteps hd1 hε.le hεd hX j)] with ω h0 h1
    exact ⟨h0, h1⟩
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine (measure_le_of_subset_union_six (fun ω hω => ?_) (hcoarse μ X hX n hn)
    (hloc' μ X hX n hn) (hmart hX n hn) (hquad hX n hn) (hvec hX n (by omega))
    (hrad' μ X hX n hn) hnull ?_)
  · by_contra hcon
    rw [Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union, Set.mem_union,
      not_or, not_or, not_or, not_or, not_or, not_or] at hcon
    obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hZ⟩ := hcon
    simp only [Set.mem_setOf_eq, not_not] at hA hB hF hZ
    simp only [Set.mem_setOf_eq, not_and, not_lt] at hD
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hC hE
    obtain ⟨-, hcard, -, hmaxLT, -, hHn⟩ := hA
    obtain ⟨h0, hs⟩ := hZ
    obtain ⟨-, hint, hglob⟩ := hB
    have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := log_add_two_nonneg
    have hlam := lam_nonneg hL0 d
    have hN0 : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hε1 : ε ≤ 1 := by
      refine hεd.le.trans ?_
      rw [div_le_one (by exact_mod_cast (by omega : 0 < d))]
      exact_mod_cast hd1
    have hbd : 2 * bd < r₀ := hr₀
    have hnorm : ∀ j, euclidNorm (X j ω) ≤ j :=
      CERW.Support.Occupation.euclidNorm_le_of_steps (fun j => X j ω) h0 hs
    have hmeas : MeasurableSet (cellSet (fun j => X j ω) n) :=
      CERW.Support.Occupation.measurableSet_cellSet _ n
    have hbdd : Bornology.IsBounded (cellSet (fun j => X j ω) n) :=
      Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 _ n)
    refine hω ?_
    unfold fluctEvent
    dsimp only
    refine ⟨⟨h0, hs⟩, hcard, hmaxLT, hHn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s t hst htn
      refine (hint s t hst htn).trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCd₁ hε.le)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact mul_le_mul_of_nonneg_right hCl₁ hlam
    · intro y hy
      exact (hglob y hy).trans (mul_le_mul_of_nonneg_right hCl₁ (error_scale_nonneg hL0 d))
    · intro y hy
      exact (hpt ε hε.le hε1 X ω h0 hnorm n (by omega) y hy).trans
        (mul_le_mul_of_nonneg_right hCp₁ hL0)
    · intro y hy
      exact le_mul_of_le_of_le hCm₁ (add_nonneg (Real.sqrt_nonneg _) hL0) (hC y hy)
    · have hpath : ∀ j ≤ n, euclidNorm (X j ω) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
        fun j hj => (CERW.euclidNorm_le_maxRadius (fun j => X j ω) hj).trans hHn
      exact le_mul_of_le_of_le hCq₁
        (add_nonneg (mul_nonneg hN0 (Real.sqrt_nonneg _)) (mul_nonneg hN0 hL0)) (hD hpath)
    · intro s t hst htn
      exact le_mul_of_le_of_le hCv₁ (Real.sqrt_nonneg _) (hE s t hst htn)
    · intro r hr hrn
      have hbdr : (bd : ℝ) < r := by exact_mod_cast (by omega : bd < r)
      have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
      have hD := sub_nonneg.mpr (CERW.Support.Geometry.tail_antitoneOn hmeas hbdd
        (Set.mem_Ioi.mpr (by linarith only [hbdr]))
        (Set.mem_Ioi.mpr (by linarith only [hbdr, hbd0]))
        (by linarith only [hbd0] : (r : ℝ) - bd ≤ r + bd))
      exact radial_le_of_le hCr₁ (Nat.cast_nonneg _) hD
        (add_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL0)) (hF r hr hrn)
  · exact ofReal_six_le hC₀.le hCl.le hCm.le hCq.le hCv.le hCr.le hnp hsum

end CERW.Support.Main
