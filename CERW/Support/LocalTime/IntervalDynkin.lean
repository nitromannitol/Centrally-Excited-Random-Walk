import CERW.Support.LocalTime.DynkinLocal
import CERW.Support.Occupation.Facts

/-!
# The Dynkin decomposition over an interval

Subtracting `eq:dynkin` at times `s ≤ t` gives, on a path from the origin,
`ℓ_{s,t}(y) = b(X_t - y) - b(X_s - y) + ε Σ_{x ∈ A_t \ A_s} u_x · Db(x - y) - (𝓜^y_t - 𝓜^y_s)`.
The sites in `A_t \ A_s` are exactly the first departures in `[s, t)`, so there are `k_{s,t}` of
them. This is the step "subtract `eq:dynkin` at `s` and `t`" of the proof of `eq:interval`.
-/

namespace CERW.Support.LocalTime

open LatticeProb Finset CERW CERW.Support.Law CERW.Support.Occupation

variable {d : ℕ}

/-- The new sites of `[s, t)` number `k_{s,t}`: `|A_t \ A_s| = k_{s,t}`. -/
theorem card_departureRange_sdiff (X : ℕ → Site d) {s t : ℕ} (hst : s ≤ t) :
    (departureRange X t \ departureRange X s).card = freshCount X s t := by
  induction t, hst using Nat.le_induction with
  | base => simp [freshCount]
  | succ n hsn ih =>
      have hIco : Finset.Ico s (n + 1) = insert n (Finset.Ico s n) := by
        ext j
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [departureRange_succ, freshCount, hIco, Finset.filter_insert]
      by_cases h : X n ∈ departureRange X n
      · rw [if_neg (not_not.mpr h), Finset.insert_eq_of_mem h]
        exact ih
      · rw [if_pos h]
        have hnot : X n ∉ departureRange X n \ departureRange X s := by
          simp [h]
        have hnot' : X n ∉ departureRange X s :=
          fun hx => h ((departureRange_mono X hsn) hx)
        rw [Finset.insert_sdiff_of_notMem (departureRange X n) hnot',
          Finset.card_insert_of_notMem hnot, ih,
          Finset.card_insert_of_notMem (by simp : n ∉ (Finset.Ico s n).filter
            fun j => X j ∉ departureRange X j)]
        rfl

/-- The interval Dynkin decomposition of `ℓ_{s,t}(y)`, for a path from the origin. -/
theorem intervalLocalTime_eq_dynkin {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) {s t : ℕ} (hst : s ≤ t) (y : Site d) :
    (intervalLocalTime (fun j => X j ω) s t y : ℝ) =
      b (X t ω - y) - b (X s ω - y) +
        ε * (∑ z ∈ departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s,
          inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y))) -
        (dynkin ε (fun z => b (z - y)) X t ω - dynkin ε (fun z => b (z - y)) X s ω) := by
  have ht := localTime_eq_dynkin hb ε X ω h0 t y
  have hs := localTime_eq_dynkin hb ε X ω h0 s y
  have hadd : ((localTime (fun j => X j ω) s y : ℕ) : ℝ) +
      (intervalLocalTime (fun j => X j ω) s t y : ℝ) =
      ((localTime (fun j => X j ω) t y : ℕ) : ℝ) := by
    exact_mod_cast localTime_add_intervalLocalTime (fun j => X j ω) hst y
  have hsub : departureRange (fun j => X j ω) s ⊆ departureRange (fun j => X j ω) t :=
    departureRange_mono _ hst
  have hsum := Finset.sum_sdiff_eq_sub hsub
    (f := fun z => inner ℝ (unitDir (toSpace z)) (centralDiff b (z - y)))
  rw [hsum, mul_sub]
  linarith [ht, hs, hadd]

end CERW.Support.LocalTime
