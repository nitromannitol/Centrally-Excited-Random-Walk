import LatticeProb.Walk.Ball
import LatticeProb.Walk.Shells

/-!
# Packing lattice sites around a point

A set of `k` lattice sites carries at most `C_d k^{1/d}` of the weight `(1 + |x - y|)^{1-d}`,
wherever the centre `y` is (`eq:packing-lattice`): the sum is largest when the sites fill a
ball around `y`.
-/

namespace CERW.Generic.Lattice

open LatticeProb

variable {d : ℕ}

/-- The sum of `(1 + |z|)^{1-d}` over the lattice ball of radius `R ≥ 0` is at most linear in
`R`. -/
theorem sum_ballFinset_rpow_one_sub_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R →
      ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (1 - (d : ℝ)) ≤ C * (R + 1) := by
  classical
  refine ⟨1 + (d : ℝ) * 2 ^ d, ?_, ?_⟩
  · have : (0 : ℝ) < 2 ^ d := by positivity
    positivity
  · intro R hR
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hexp : (1 : ℝ) - (d : ℝ) ≤ 0 := by linarith
    have hstep1 : ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (1 - (d : ℝ))
        ≤ ∑ z ∈ ballFinset d R, (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ)) := by
      refine Finset.sum_le_sum fun z _ => ?_
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hexp
      have h1 := supNorm_le_euclidNorm z
      linarith
    have hstep2 : ∑ z ∈ ballFinset d R, (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ))
        ≤ ∑ z ∈ boxFinset (0 : Site d) ⌊R⌋₊,
            (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro z hz
        rw [ballFinset] at hz
        exact (Finset.mem_filter.mp hz).1
      · intro z _ _
        exact Real.rpow_nonneg (by positivity) _
    have hstep3 := sum_box_radial_le (d := d) (fun k => (1 + (k : ℝ)) ^ (1 - (d : ℝ)))
        (fun k => Real.rpow_nonneg (by positivity) _) ⌊R⌋₊
    have hstep3' : ∑ z ∈ boxFinset (0 : Site d) ⌊R⌋₊,
            (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ))
        ≤ 1 + ∑ k ∈ Finset.Icc 1 ⌊R⌋₊,
            2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)
              * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) := by
      simpa only [Nat.cast_zero, add_zero, Real.one_rpow] using hstep3
    have hterm : ∀ k ∈ Finset.Icc 1 ⌊R⌋₊,
        2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)
            * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) ≤ (d : ℝ) * 2 ^ d := by
      intro k hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hk).1
      have ha : (0 : ℝ) < 1 + (k : ℝ) := by linarith
      have hb : (0 : ℝ) ≤ 2 * (k : ℝ) + 1 := by linarith
      have hle : 2 * (k : ℝ) + 1 ≤ 2 * (1 + (k : ℝ)) := by linarith
      have hpow : (2 * (k : ℝ) + 1) ^ (d - 1)
          ≤ (2 * (1 + (k : ℝ))) ^ (d - 1) :=
        pow_le_pow_left₀ hb hle (d - 1)
      have hmul : (2 * (1 + (k : ℝ))) ^ (d - 1)
          = (2 : ℝ) ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) :=
        mul_pow 2 (1 + (k : ℝ)) (d - 1)
      have hpow' : (2 * (k : ℝ) + 1) ^ (d - 1)
          ≤ (2 : ℝ) ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := by
        rw [← hmul]
        exact hpow
      have hcomb : (1 + (k : ℝ)) ^ (d - 1)
          * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) = 1 := by
        rw [show (1 + (k : ℝ)) ^ (d - 1)
            = (1 + (k : ℝ)) ^ (((d - 1 : ℕ)) : ℝ) from (Real.rpow_natCast _ _).symm]
        rw [← Real.rpow_add ha]
        have hsum : (((d - 1 : ℕ)) : ℝ) + (1 - (d : ℝ)) = 0 := by
          rw [Nat.cast_sub hd]; ring
        rw [hsum, Real.rpow_zero]
      have h2d : 2 * (2 : ℝ) ^ (d - 1) = (2 : ℝ) ^ d := by
        conv_lhs => rw [← pow_succ' (2 : ℝ) (d - 1)]
        congr 1
        omega
      calc 2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)
              * (1 + (k : ℝ)) ^ (1 - (d : ℝ))
          ≤ 2 * (d : ℝ) * ((2 : ℝ) ^ (d - 1)
              * (1 + (k : ℝ)) ^ (d - 1))
              * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left hpow' (by positivity)
        _ = 2 * (d : ℝ) * (2 : ℝ) ^ (d - 1)
              * ((1 + (k : ℝ)) ^ (d - 1)
                * (1 + (k : ℝ)) ^ (1 - (d : ℝ))) := by ring
        _ = 2 * (d : ℝ) * (2 : ℝ) ^ (d - 1) := by rw [hcomb, mul_one]
        _ = (d : ℝ) * 2 ^ d := by rw [← h2d]; ring
    have hIcc : ∑ k ∈ Finset.Icc 1 ⌊R⌋₊,
        2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)
            * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) ≤ (⌊R⌋₊ : ℝ) * ((d : ℝ) * 2 ^ d) := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
      rw [nsmul_eq_mul]
    have hfloor : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR
    calc ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (1 - (d : ℝ))
        ≤ ∑ z ∈ ballFinset d R, (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ)) := hstep1
      _ ≤ ∑ z ∈ boxFinset (0 : Site d) ⌊R⌋₊,
            (1 + (supNorm z : ℝ)) ^ (1 - (d : ℝ)) := hstep2
      _ ≤ 1 + ∑ k ∈ Finset.Icc 1 ⌊R⌋₊,
            2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)
              * (1 + (k : ℝ)) ^ (1 - (d : ℝ)) := hstep3'
      _ ≤ 1 + (⌊R⌋₊ : ℝ) * ((d : ℝ) * 2 ^ d) := by linarith [hIcc]
      _ ≤ 1 + R * ((d : ℝ) * 2 ^ d) := by
            have hD : 0 ≤ (d : ℝ) * 2 ^ d := by positivity
            nlinarith
      _ ≤ (1 + (d : ℝ) * 2 ^ d) * (R + 1) := by
            have hD : 0 ≤ (d : ℝ) * 2 ^ d := by positivity
            nlinarith

/-- The packing bound `eq:packing-lattice`: a set of `k` lattice sites carries at most
`C_d k^{1/d}` of the weight `(1 + |x - y|)^{1-d}`, uniformly in the centre `y`. -/
theorem sum_rpow_one_sub_le_card_rpow (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Site d)) (y : Site d),
      ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) ≤ C * (E.card : ℝ) ^ ((1 : ℝ) / d) := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sum_ballFinset_rpow_one_sub_le (d := d) hd
  refine ⟨2 * C₁ + 1, by linarith, ?_⟩
  intro E y
  have hexp : (1 : ℝ) - (d : ℝ) ≤ 0 := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rcases Nat.eq_zero_or_pos E.card with hk0 | hkpos
  · have hE : E = ∅ := Finset.card_eq_zero.mp hk0
    rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero, Finset.sum_empty]
    rw [Real.zero_rpow]
    · simp
    · have hdR : (d : ℝ) ≠ 0 := by
        exact ne_of_gt (by exact_mod_cast (by omega : 0 < d))
      exact div_ne_zero one_ne_zero hdR
  · have hkposR : (0 : ℝ) < (E.card : ℝ) := by exact_mod_cast hkpos
    have hk1R : (1 : ℝ) ≤ (E.card : ℝ) := by
      have h1 : (1 : ℕ) ≤ E.card := by omega
      exact_mod_cast h1
    set R : ℝ := (E.card : ℝ) ^ ((1 : ℝ) / d) with hRdef
    have hR1 : 1 ≤ R := by
      rw [hRdef]
      exact Real.one_le_rpow hk1R (by positivity)
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hRnonneg : 0 ≤ R := le_of_lt hRpos
    set S : Finset (Site d) := E.filter (fun x => euclidNorm (x - y) ≤ R) with hSdef
    set T : Finset (Site d) := E.filter (fun x => ¬ (euclidNorm (x - y) ≤ R)) with hTdef
    have hsplit : (∑ x ∈ S, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)))
        + (∑ x ∈ T, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)))
        = ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
      rw [hSdef, hTdef]
      exact Finset.sum_filter_add_sum_filter_not E (fun x => euclidNorm (x - y) ≤ R) _
    have hnear : ∑ x ∈ S, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) ≤ 2 * C₁ * R := by
      have hinj : Set.InjOn (fun x : Site d => x - y) ↑S :=
        fun a _ b _ hab => sub_left_injective hab
      have himage : ∑ x ∈ S, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ))
          = ∑ z ∈ S.image (fun x => x - y), (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
        (Finset.sum_image (f := fun z => (1 + euclidNorm z) ^ (1 - (d : ℝ))) hinj).symm
      rw [himage]
      have hsub : S.image (fun x : Site d => x - y) ⊆ ballFinset d R := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        rw [mem_ballFinset_iff]
        exact (Finset.mem_filter.mp hx).2
      calc ∑ z ∈ S.image (fun x : Site d => x - y), (1 + euclidNorm z) ^ (1 - (d : ℝ))
          ≤ ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun z _ _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _)
        _ ≤ C₁ * (R + 1) := hC₁ R hRnonneg
        _ ≤ 2 * C₁ * R := by nlinarith [hC₁pos, hR1]
    have hfar : ∑ x ∈ T, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ))
        ≤ (E.card : ℝ) ^ ((1 : ℝ) / d) := by
      have hterm : ∀ x ∈ T, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ))
          ≤ R ^ (1 - (d : ℝ)) := by
        intro x hx
        have hxl : ¬ (euclidNorm (x - y) ≤ R) := (Finset.mem_filter.mp hx).2
        have hRlt : R < euclidNorm (x - y) := lt_of_not_ge hxl
        have h1 : (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) ≤ (1 + R) ^ (1 - (d : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [hRpos]) (by linarith) hexp
        have h2 : (1 + R) ^ (1 - (d : ℝ)) ≤ R ^ (1 - (d : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hRpos (by linarith) hexp
        linarith
      have hcard : (T.card : ℝ) ≤ (E.card : ℝ) := by
        have h1 : T.card ≤ E.card := by
          rw [hTdef]
          exact Finset.card_filter_le E _
        exact_mod_cast h1
      have hkR : (E.card : ℝ) * R ^ (1 - (d : ℝ))
          = (E.card : ℝ) ^ ((1 : ℝ) / d) := by
        rw [hRdef]
        have hmul : ((E.card : ℝ) ^ ((1 : ℝ) / d)) ^ (1 - (d : ℝ))
            = (E.card : ℝ) ^ (((1 : ℝ) / d) * (1 - (d : ℝ))) :=
          (Real.rpow_mul hkposR.le ((1 : ℝ) / d) (1 - (d : ℝ))).symm
        rw [hmul]
        nth_rewrite 1 [← Real.rpow_one (E.card : ℝ)]
        rw [← Real.rpow_add hkposR]
        congr 1
        have hdR : (d : ℝ) ≠ 0 := by
          exact ne_of_gt (by exact_mod_cast (by omega : 0 < d))
        field_simp
        ring
      calc ∑ x ∈ T, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ))
          ≤ T.card • (R ^ (1 - (d : ℝ))) := Finset.sum_le_card_nsmul T _ _ hterm
        _ = (T.card : ℝ) * R ^ (1 - (d : ℝ)) := by rw [nsmul_eq_mul]
        _ ≤ (E.card : ℝ) * R ^ (1 - (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hRnonneg _)
        _ = (E.card : ℝ) ^ ((1 : ℝ) / d) := hkR
    rw [← hsplit]
    refine (add_le_add hnear hfar).trans ?_
    rw [hRdef]
    linarith

end CERW.Generic.Lattice
