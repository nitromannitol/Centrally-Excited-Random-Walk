I read the paper statements, the Lean anchors, and the supporting Lean definitions (`Space`, `Kernel`, `Law`, `Occupation`, `Potential`, plus `LatticeProb`'s `srwGreen`/`srwGreenInf` and `Measure.toSphere`).

## 1. `LatticePotentialKernel` — no discrepancy found
- d=2: `2/Real.pi * log(euclidNorm x) + κ`, error `euclidNorm x ^ (-2)`, and `b x = lim (srwGreen 2 M 0 - srwGreen 2 M x)`. This is exactly `eq:kernel-asymptotics` for the potential kernel normalized by `b(0)=0` (the finite-difference Green limit satisfies `(P-I)b=δ₀`, `b(0)=0`).
- d≥3: the line states the asymptotics of `srwGreenInf = G`, with `+2/(((d:ℝ)-2)*ωd) * |x|^(2-d)` and error `|x|^{-(d:ℝ)}`. The paper defines `b=-G` and states `b = -2/((d-2)ω_d)|x|^{2-d}+O(|x|^{-d})`; substituting `b=-G` gives precisely the Lean line. The `2/π`, `2/((d-2)ω_d)`, exponents `-2`, `2-d`, `-d` all match.

## 2. `ball_shape` — no discrepancy found
- `a=((d+1)/(2*d*ε*ωd))^(1/(d+1))`, `N n = n^(1/(d+1))`, profile `2*d*ε*max(a-|x|/N)0`, range limit `ω_d a^d`, fixed-`x` limit `2*d*ε*a`, inner/outer balls `(a±η)N`, recurrence `∃ᶠ j, X j ω = x`. All match `thm:shape`; sup→0 is rendered as the approved `∀η>0, ∀ᶠn, ∀x, |·|≤η`.

## 3. `fluctuation_bounds` — no discrepancy found
- `Q = (L/N)^(1/2)` for `d=2`, `(L/N)^(d/(2d-1))` otherwise; inner `a-CQ`, outer `a+CQ^{1/d}L`; volume+`|A_n|/N^d-ω_da^d|≤CQ`; profile `CQ^{1/d}`; plus the a.s. eventual conjunct. All match `thm:fluctuations` (probability as a bad-event bound).

## 4. `hausdorff_bound` — no discrepancy found
- `d=2`: `n^(-1/12) L^(5/4)`; `d≥3`: `n^(-1/((d+1)(2d-1))) L^(2d/(2d-1))`. Planar inner-radius `a*N - C*n^(1/6)*sqrt L`. `hausdorffEDist` against `Metric.closedBall 0 a` = `\overline B(0,a)`, and the scaled set is `N⁻¹ • V_n`. Matches `eq:hausdorff` and the planar remark.

## 5. `local_time_potential` — no discrepancy found
- `maxLocalTime ≤ Cd*ε*|A_n|^(1/d)+Cλ`, interval `≤ Cd*ε*k_{s,t}^(1/d)+Cλ`, `|ℓ̃_n - U_{D_n}| ≤ C e_n(M_n)`; `λ = L^2` (d=2) else `L`; `e(m)=√m·L+L` (d=2) else `√(m·L)+L`; `Cd` bound before `ε`. Matches `lem:local` (including `|y|≤2n`).

## 6. `potential_geometry` — no discrepancy found
- `‖U_D‖≤Cd ε R^(1/d)`, Hölder `Cd ε R^(1/(2d))|y-z|^(1/2)`, spherical identity `(dωd)⁻¹∫U_D(sθ) = 2dε F(s)`, ball `2dε(b-|y|)_+`. `Measure.toSphere` is the unnormalised surface measure with total mass `dω_d=σ_d`, and `tail=(dω_d)⁻¹∫_{D∩{|v|>s}}|v|^{1-d}`, so the normalisations match `lem:geometry`/`eq:Fmass`.

## 7. `radial_test` — no discrepancy found
- `b_d=⌈√d/2⌉+6`, `r₀>2b_d`, `M_sh(r)=max_{|‖x‖-r|≤3}ℓ_n(x)`, and
  `F(r+b_d) ≤ C M_sh(r)[F(r-b_d)-F(r+b_d)] + C[√(M_n r^{1-d}F(r-b_d)L) + r^{1-d}L]`.
  Errors `r^{1-d}L` and `√(M_n r^{1-d}F(r-b_d)L)`, both `b_d` shifts, and the `r₀≤r≤n` range match `lem:radial` (with the shell width `3`).

## 8. `coarse_bounds` — no discrepancy found
- `cN^d≤|A_n|≤CN^d`, `cN≤M_n≤CN`, `cN≤H_n≤CN`, `N=n^{1/(d+1)}`; `departureRange.card=|A_n|`, `maxLocalTime=M_n`, `maxRadius=max_{0≤j≤n}|X_j|=H_n`. Matches `prop:coarse`.

**Adversarial note (not a defect):** the `d≥3` line of `LatticePotentialKernel` is written for `srwGreenInf=G` rather than for `b`. Because the paper fixes `b=-G`, the displayed positive coefficient and exponent are exactly `eq:kernel-asymptotics` after the sign substitution, so it is not a discrepancy.

Overall: I could not refute any of the eight declarations; every formula, exponent, normalisation, and quantifier I was asked to focus on agrees with the paper.
