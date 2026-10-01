# External sources audit: `MartingaleCLT` and `StoutLIL`

Scope: read-only comparison of the two cited theorems (Hall-Heyde 1980, Cor. 3.1 / Thm 3.2; Stout 1970, Thm 1 / Stout 1974, Thm 5.4.1)
with the Lean propositions `CERW.Support.Statements.MartingaleCLT` and `StoutLIL`
(`CERW/Support/Statements.lean`, lines 23-35 and 37-52; `CERW.predBracket` in `CERW/Model/Bracket.lean`).

## Verdicts

* **MartingaleCLT: IMPLIED-WITH-REMARK.** It is the special case `k_n = n`, `F_{n,i} = F_i` (so nesting holds with equality), `X_{ni} = (S_i - S_{i-1})/s_n`,
  constant `eta^2 = v >= 0`, conclusion weakened from stable convergence to convergence in law. Remarks: (a) `F_0` need not be trivial in Lean; prepend one zero term
  (harmless, see 2.3); (b) `v = 0` is covered by Hall-Heyde as restated (`eta^2` only "a.s. finite"), and independently by a two-line argument (see 2.4), so nothing depends on
  whether Hall-Heyde exclude `eta^2 = 0`.
* **StoutLIL: IMPLIED-WITH-REMARK.** Put `K_n := B_n u_n / s_n` (with the repo's `max(., e^e)` convention for small `n`); this is `F_{n-1}`-measurable, tends to `0` a.s., and the bound holds for all `n`. The remark is
  that this needs Stout's hypothesis to be the predictable (`F_{n-1}`-measurable, random) `K_n`; that form is confirmed only through restatements (3.1), not through Stout's own text, which I could not reach.
  If Stout's theorem were only for deterministic `K_n` the verdict would drop to NOT IMPLIED (fix: require `B n` deterministic, or find a source for predictable `K_n`); the evidence says it is not.

**Access caveat (important).** I could not read any of the four primary texts (Hall-Heyde book, Stout 1970, Stout 1974, Stout 1973). Attempts and outcomes are in section 0.
Every quote below is therefore from a restatement or a secondary source, each labelled PRIMARY-TEXTBOOK / RESTATEMENT / CITATION-ONLY. No quote is reproduced from memory; where I recall
something from memory, it is marked "memory".

---

## 0. What I could and could not reach

| Source | Outcome |
|---|---|
| Hall-Heyde book, Kobo/pageplace preview PDF (`api.pageplace.de/preview/DT0400.9781483263229_A23867795/preview-9781483263229_A23867795.pdf`) | Opened (17 pages: front matter, contents, notation, start of Ch. 1). Contents confirm: Ch. 3 = "The Central Limit Theorem", 3.2 at p. 52; 4.4 = "The Law of the Iterated Logarithm and Its Invariance Principle" at p. 115. **No Ch. 3 or Ch. 4 text.** |
| Google Books (`xxbvAAAAMAAJ`, `gqriBQAAQBAJ`) | "No eBook"/viewing limit reached; snippet and text endpoints answer with a bot-check. Not pursued further. |
| archive.org | No full text of Hall-Heyde. Stout 1974 exists as a lending item `almostsureconver0000stou` (restricted; not borrowed, search-inside refused). |
| Stout 1970 (`link.springer.com/article/10.1007/BF00533299`) | Springer returns a JavaScript client challenge; not bypassed. zbMATH record Zbl 0209.49004 exists (no review text; 8 references: Chow-Robbins-Teicher 1965, Doob, Feller 1943, Kolmogorov 1929, Levy, Loeve, Marcinkiewicz-Zygmund 1937, Strassen 1965). MR0293701. |
| Stout 1973 (Ann. Probab. 1, 322-328, upper-half LIL for supermartingales) | Project Euclid bot-blocked; only the abstract is visible: "These two maximal inequalities are used to derive upper half laws of the iterated logarithm for supermartingales, multiplicative random variables, and random variables not satisfying particular dependence assumptions." |
| Hall-Heyde Chapter 3 Remarks (p. 59, including the remark on `eta^2` constant) | **Not read.** Only indirect evidence, see 1.4. |

I did not try to get around paywalls or bot protection.

---

## 1. Hall and Heyde (1980), Theorem 3.2 and Corollary 3.1

### 1.1 Restatements read (with type)

**S2. RESTATEMENT (near-verbatim copy, transcription typos).** arXiv:2501.16526, "Ancestral Inference and Learning for Branching Processes in Random Environments", Appendix C.7 "Results from literature", p. 62-63.
(Wording as printed, including its typos "s.s.", "Linderberg", "Lemma C.4"; mathematical symbols transliterated to ASCII by me. The same transliteration applies to every quote below.)

> Theorem C.4 (Theorem 3.2 in Hall and Heyde (1980)). Let {S_ni, F_ni, 1 <= i <= k_n, n >= 1} be a zero-mean, square-integrable martingale array with differences X_ni, and let eta^2 be an s.s. finite r.v.
> Suppose that max_{1<=i<=k_n} |X_ni| ->P 0 (62), sum_i X_ni^2 ->P eta^2 (63), E(max_{1<=i<=k_n} X_ni^2) is bounded in n (64), and the sigma-fields are nested: F_{n,i} subset-or-equal F_{n+1,i} for 1 <= i <= k_n, n >= 1 (65).
> Then S_{n k_n} = sum_i^{k_n} X_ni ->d Z (stably), where the r.v. Z has characteristic function E[exp(-1/2 eta^2 t^2)].
>
> Corollary C.4.1 (Corollary 3.1 in Hall and Heyde (1980)). If (62) and (64) are replaced by the Linderberg condition: for all eps > 0, sum_i^{k_n} E[X_ni^2 I(|X_ni| > eps) | F_{n,i-1}] ->P 0 (66),
> if (63) is replaced by the analogous condition on the conditional variance: V_{n k_n}^2 = sum_{i=1}^{k_n} E[X_ni^2 | F_{n,i-1}] ->P eta^2 (67), and if (65) holds, then the conclusion of Lemma C.4 remains true.

**S3. RESTATEMENT of Theorem 3.2's conditions, with explicit comments on condition (3.21).** Kuersteiner and Prucha (2013), J. Econometrics 174, 107-126
(`econweb.umd.edu/~prucha/papers/JE174(2013).pdf`), Section 2.2 (their Theorem 1, a non-nested variant). Quotes:

> "The conditions imposed in Theorem 1 are identical to the conditions of Hall and Heyde (1980, Theorem 3.2, p. 58) except for their condition (3.21) postulating F_nv subset-or-equal F_{n+1,v}, which we do not require. On the other hand, our conclusion is weaker because we only establish F_0-stable rather than F-stable convergence."
> "The corollary after Theorem 3 in Eagleson (1975) maintains an identical catalog of assumptions as Hall and Heyde (1980, Corollary 3.1, p. 58) except for their condition (3.21)."
> Theorem 1 (theirs): "... zero mean, square integrable martingale array ... let eta^2 be an a.s. finite random variable measurable w.r.t. F_0. If max_v |X_nv| ->p 0 (14), sum_v X_nv^2 ->p eta^2 (15) and E[max_v X_nv^2] is bounded in n (16) then S_{n k_n} ->d Z (F_0-stably) where the random variable Z has characteristic function E exp(-1/2 eta^2 t^2). In particular, S_{n k_n} ->d eta xi (F_0-stably) where xi ~ N(0,1) is independent of eta."
> "We note that when F_0 = {0, Omega}, F_0-stable convergence is convergence in distribution."
> "The nesting condition F_nv subset-or-equal F_{n+1,v} may be quite natural in a time series setting but does not hold for panel data with increasing cross-sectional sample size."

So the Hall-Heyde condition labels are: (3.18)-(3.20) the three Theorem 3.2 conditions, (3.21) = nesting, and in this source the nesting condition is indexed over `v >= 1` (no condition on `F_{n0}`).

**S4. RESTATEMENT (special case, single filtration).** arXiv:2405.20311, Theorem 5.1 (p. 31), introduced as "The following is a special case of [HH, Theorem 3.2 and Corollary 3.1]":

> For each n, let (M_{n,j})_{j<=k_n} be a real-valued, mean-zero and square integrable martingale with respect to the filtration (F_j)_j, and Delta_{n,j} := M_{n,j} - M_{n,j-1} ... (a) V_n := sum_j E[|Delta_{n,j}|^2 | F_{j-1}] ->p V_infty. (b) The conditional Lindeberg condition holds: for any delta > 0, sum_j E[|Delta_{n,j}|^2 1{|Delta_{n,j}| > delta} | F_{j-1}] ->p 0.
> Then M_{n,k_n} ->d sqrt(V_infty) G where G ~ N(0,1) is independent of V_infty, and the convergence in law is also stable.

**S5. RESTATEMENT (single filtration, constant limit, explicitly allows 0).** arXiv:1903.08507, Theorem 15 (p. 21-22):

> Theorem 15. (Hall and Heyde, 1980, Corollary 3.1) Let (w_{n,i})_{1<=i<=n, n>=1} be a triangular array of random variables such that E[w_{n,i} | F_{i-1}] = 0 for all 1 <= i <= n (22), sum_i E[w_{n,i}^2 | F_{i-1}] -> v* >= 0 in probability (23), sum_i E[w_{n,i}^2 I{|w_{n,i}| > eps} | F_{i-1}] -> 0 in probability (24), then sum_i w_{n,i} converges in distribution to N(0, v*).
(The arrow symbol and "for every eps" are lost in the text layer; the statement is as printed otherwise.)

**S6. RESTATEMENT of the constant-limit, non-nested case (Brown 1971).** Azrak-Melard, "An Alternative Central Limit Theorem for Martingale Difference Arrays" (dipot.ulb.ac.be/dspace/bitstream/2013/172397/2/AAHM_v8_2.pdf), Theorem 2.1 "due to Brown (1971)": for an array with arbitrary `F_{k,T}` per `T`,
(i) for every eps > 0, (1/T) sum_k E[Y_{k,T}^2 I{|Y_{k,T}| > eps sqrt(T)} | F_{k-1,T}] -> 0 in probability, (ii) (1/T) sum_k E[Y_{k,T}^2 | F_{k-1,T}] -> 1 in probability, then T^{-1/2} sum_k Y_{k,T} -> N(0,1) in distribution. No nesting.
Also Arlotto-Steele, arXiv:1505.00749, Proposition 5 ("array of MDS ... w.r.t. filtration {G_{n,i}: 0 <= i <= n}", conditional variances -> 1, negligibility) followed by
"This version is easily covered by any of the martingale central limit theorems of Brown (1971), McLeish (1974), or Hall and Heyde (1980, Corollary 3.1)." (Their `F_{n,i} = sigma(X_{n,1..i})` is not nested in `n`.)

**S7. PRIMARY-TEXTBOOK (constant-limit, non-nested, but functional form).** Durrett, *Probability: Theory and Examples*, 5th ed. (version of 11 Jan 2019, `services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf`), Section 8.2, read directly:

> "We say that X_{n,m}, F_{n,m}, 1 <= m <= n, is a martingale difference array if X_{n,m} in F_{n,m} and E(X_{n,m} | F_{n,m-1}) = 0 for 1 <= m <= n, where F_{n,0} = {empty, Omega}."
> "Theorem 8.2.4. Lindeberg-Feller theorem for martingales. Suppose X_{n,m}, F_{n,m}, 1 <= m <= n is a martingale difference array. If (i) V_{n,[nt]} -> t in probability for all t in [0,1] and (ii) for all eps > 0, sum_{m<=n} E(X_{n,m}^2 1(|X_{n,m}| > eps) | F_{n,m-1}) -> 0 in probability, then S_{n,(n.)} => B(.)."
Note (i) is for all `t`, so this does not by itself give the single-time statement of the Lean Prop; it is listed only as evidence that per-row filtrations with constant limit need no nesting.

**S8. RESTATEMENT with a discrepancy.** Remillard-Vaillancourt, arXiv:2506.22354, Proposition 3.1, introduced as "a sample result (Hall and Heyde, 1980, Corollary 3.1)":
"Assume that the sigma-algebras are nested: G_{n,k} subset-or-equal G_{n+1,k} for all n >= 1 and all 1 <= k <= n. Assume that A_n(1) ->Pr eta as n -> infinity, for some random variable eta such that P{eta in (0,infinity)} = 1. Suppose also that, for any eps > 0, sum_j E[X_{n,j}^2 I(|X_{n,j}| > eps) | G_{n,j-1}] ->Pr 0. Then M_n(1) ->Law Z sqrt(eta)..., where Z ~ N(0,1) is independent of eta."
and "In Hall and Heyde (1980, Corollary 3.1) the conclusion is stated for (the stronger) stable convergence."
This source puts `P{eta in (0, infinity)} = 1`, whereas S2 and S3 say only "a.s. finite" and S5 says `v* >= 0`. See 1.3.

**S9. CITATION-ONLY.**
* Hall (1984), J. Multivariate Anal. 14, 1-16 (`aaradill.github.io/hall_1984.pdf`): "We shall apply Brown's [3] Martingale central limit theorem; see Hall and Heyde [9, Corollary 3.1, p. 58]." (Hall is a coauthor; he applies it to `s_n^{-1} U_n` with conditional Lindeberg and conditional variance -> 1.)
* Zhang-Mykland-Ait-Sahalia, arXiv:math/0411397: "Corollary 3.1 (p. 58-59) of Hall and Heyde (1980)" and "Corollary 3.1 and the Remarks following this corollary (p. 58-59)". (So the Remarks after Cor. 3.1 are on p. 59.)
* Kuersteiner-Prucha (S3) also refer to "Hall and Heyde's comment on Eagleson's result (see Hall and Heyde, 1980, p. 59)".
* Dedecker-Merlevede (helios2.mi.parisdescartes.fr/~jdedecke/a4.pdf): the Lindeberg-type condition is discussed "p. 53 in Hall and Heyde (1980)".
* Aldous's MathSciNet review (MR0624435): "McLeish's slick characteristic function proof of the basic result is used, and there follows discussion of convergence to mixtures of normals" (no statement).

### 1.2 Reconstructed statement of Corollary 3.1

Combining S2 (verbatim copy) with S3 (independent confirmation of the Theorem 3.2 half and of the label (3.21)):

Let `{S_ni, F_ni, 1 <= i <= k_n, n >= 1}` be a zero-mean, square-integrable martingale array with differences `X_ni`, and `eta^2` an a.s. finite r.v.
If (Lindeberg, conditional) for all `eps > 0`, `sum_i E[X_ni^2 I(|X_ni| > eps) | F_{n,i-1}] ->P 0`; (variance) `V^2_{n k_n} = sum_i E[X_ni^2 | F_{n,i-1}] ->P eta^2`;
(nesting, condition (3.21)) `F_{n,i} subset-or-equal F_{n+1,i}`, `1 <= i <= k_n`, `n >= 1`;
then `S_{n k_n} ->d Z` (stably), `Z` having characteristic function `E exp(-1/2 eta^2 t^2)`, i.e. `Z = eta * N(0,1)` with `N(0,1)` independent of `eta` (S3, S4, S8).
Corollary 3.1 is Theorem 3.2 with the two hypotheses "max |X_ni| ->P 0" and "E max X_ni^2 bounded" replaced by the conditional Lindeberg condition, and "sum X_ni^2 ->P eta^2" replaced by the conditional-variance condition (S2, Cor. C.4.1).

### 1.3 Is `eta^2 = 0` allowed?

* As restated by S2 and S3 the only requirement on `eta^2` is "a.s. finite random variable" (S3 adds `F_0`-measurability for its non-nested variant). The constant `0` is such a variable, and `E exp(-1/2 * 0 * t^2) = 1` is the characteristic function of `delta_0`.
* S5 writes the limit as `v* >= 0` explicitly; S4 writes `sqrt(V_infty) G` with no positivity.
* S8 adds `P{eta in (0,infinity)} = 1`. I read this as their own application-driven restriction (it is not in S2/S3), but I cannot exclude that it was copied from the book.
* Because of that one discrepancy I do **not** rely on the book for `v = 0`: section 2.4 gives a self-contained proof of the `v = 0` case of the Lean Prop (it needs neither Lindeberg nor nesting).

### 1.4 Is nesting needed when `eta^2` is constant?

I did not read Hall-Heyde's Remarks after Cor. 3.1 (p. 59) and so cannot quote them. Evidence that it is not needed for constant `eta^2`: Brown (1971) in S6 (arbitrary `F_{k,T}`, constant limit 1, conditional Lindeberg);
Arlotto-Steele (S6) say the non-nested constant-limit statement is "easily covered by any of ... Brown (1971), McLeish (1974), or Hall and Heyde (1980, Corollary 3.1)";
Kuersteiner-Prucha's Theorem 1 (S3) proves the Theorem 3.2 conditions without (3.21) and with `F_0`-stable convergence, which for trivial `F_0` (constant `eta^2`) is convergence in distribution;
Durrett 8.2.4 (S7). My memory (unverified) is that Hall-Heyde's Remarks state exactly this for constant `eta^2`, which is consistent with Zhang-Mykland-Ait-Sahalia citing "Corollary 3.1 and the Remarks following this corollary".
**This question is moot for the Lean Prop**: there `F_{n,i} = F_i` for all `n`, so `F_{n,i} = F_{n+1,i}` and (3.21) holds literally.

---

## 2. `MartingaleCLT` against Hall-Heyde

### 2.1 Translation (Lean -> Hall-Heyde array)

| Lean | Hall-Heyde |
|---|---|
| `mu` probability measure, `S : N -> Omega -> R`, `Martingale S F mu`, `forall n, MemLp (S n) 2 mu`, `S 0 = 0` | `k_n = n`, `F_{n,i} := F_i` (`i >= 1`), `X_{ni} := (S_i - S_{i-1})/s_n`, `S_{ni} = S_i/s_n`: zero-mean (from `S_0 = 0` and martingale), square-integrable martingale array |
| `s : N -> R`, `0 < s n` | normalisation absorbed in `X_{ni}`; only `n >= 1` matters |
| Lindeberg hypothesis: `TendstoInMeasure mu (n |-> sum_{i<n} mu[((S(i+1)-S i)/s n)^2 * 1{delta < |S(i+1)-S i|/s n} | F i]) atTop 0` for every `delta > 0` | `sum_{i=1}^n E[X_ni^2 I(|X_ni| > eps) | F_{n,i-1}] ->P 0` (Lean index `i` = HH index `i+1`; strict `>`, conditioning on `F_{n,i-1} = F_{i-1}` = Lean `F i`) |
| variance hypothesis: `TendstoInMeasure mu (n |-> predBracket mu F S S n / s n ^ 2) atTop (const v)`, `v : R>=0`; `predBracket ... n = sum_{t<n} mu[(S(t+1)-S t)^2 | F t]` | `V^2_{nn} = sum_i E[X_ni^2 | F_{n,i-1}] ->P eta^2` with `eta^2 = v` constant (`^` binds tighter than `/`, so the division is `.../ (s n ^ 2)`, correct) |
| conclusion `TendstoInDistribution (n w |-> S n w / s n) atTop id (fun _ => mu) (gaussianReal 0 v)` | `S_{n k_n} ->d Z`, `Z` with ch.f. `exp(-v t^2/2)`, i.e. `N(0,v)`; Mathlib `gaussianReal 0 0 = dirac 0` (`gaussianReal_zero_var`) |
| `TendstoInMeasure` is defined with outer measure and `edist` (Mathlib `ConvergenceInMeasure.lean` line 57-59) | convergence in probability; conditional expectations are a.e.-defined, and convergence in measure does not see the choice of version |

### 2.2 Points where the Lean version is a stronger claim than the source (Lean hypotheses weaker than Hall-Heyde's)

1. `F_0` (Lean `F 0`) need not be trivial; `S 0 = 0` and `E[S_1 | F_0] = 0`, and the `i = 1` terms of the bracket and Lindeberg sums are `F_0`-conditional. Hall-Heyde's arrays have a `sigma`-field `F_{n,0}` in the conditioning for `i = 1`, whose convention I could not check (the restatements are silent; Kuersteiner-Prucha carry `F_{n0}` explicitly; Durrett takes it trivial). Handled by the remark 2.3; it costs nothing in either convention.
2. Nothing else. In particular: no moment bound beyond `L^2`, no maximal bound, no `k_n -> infinity` needed (S3 adds `k_n -> infinity` for its own theorem; here `k_n = n`).

### 2.3 Remark used: prepend a zero term

If Hall-Heyde's array requires a trivial `F_{n,0}`: define `F'_{n,0} = {empty, Omega}`, `X'_{n,1} := 0`, `F'_{n,1} := F_0`, and for `i >= 1`: `X'_{n,i+1} := X_{ni}`, `F'_{n,i+1} := F_i`, `k'_n = n + 1`.
Then `E[X'_{n,1} | F'_{n,0}] = 0`, `E[X'_{n,2} | F'_{n,1}] = E[X_{n,1} | F_0] = 0`, the Lindeberg and bracket sums are unchanged (the extra term is 0), and `F'_{n,i} = F'_{n+1,i}` so (3.21) holds. The limit statement is unchanged.

### 2.4 Remark used: the case `v = 0` needs no theorem

If `predBracket_n / s_n^2 ->P 0`, then `S_n/s_n ->P 0` (hence `->d dirac 0 = gaussianReal 0 0`), by stopping: fix `n`, put `M_k = S_k/s_n`, `A_k = predBracket_k/s_n^2` (`A_{k+1}` is `F_k`-measurable), and `tau := min(n, inf{k : A_{k+1} > d})`, a stopping time.
Then `A_{tau} <= d` and `E[M_{tau}^2] = E[A_tau] <= d` (orthogonality of increments, conditional variance sums), and `{tau < n} = {A_n > d}`. So `P(|M_n| > e) <= P(A_n > d) + d/e^2`; let `n -> infinity`, then `d -> 0`. No Lindeberg condition and no nesting are used.

### 2.5 Points where the Lean version is stronger than needed (Lean asks more than Hall-Heyde; harmless)

* Constant limit `v : R>=0`, not a random `eta^2`; consequently the conclusion is convergence in law to `N(0,v)`, not stable convergence to a mixture.
* One martingale `S` with one filtration `F` and one deterministic normaliser `s_n` (so `F_{n,i} = F_i`; nesting is an equality).
* `S 0 = 0` everywhere (arrays conventionally start at `S_{n0} = 0`; not checked in the book) and `Martingale` with `MemLp 2` for every `n`.
* `0 < s n` for every `n` including `n = 0, 1`; a consumer that has `s n = 0` for finitely many `n` must change finitely many values (hypotheses and conclusion are `atTop`-statements, so this is a legitimate standard remark; `forall^f n in atTop, 0 < s n` would be the natural form). Already noted in `draft-audit-1.md` section 7.
* The Lindeberg hypothesis is demanded for every `delta > 0` (same as Hall-Heyde).

**Verdict: IMPLIED-WITH-REMARK** (remarks 2.3 and 2.4; both optional depending on conventions and on whether `eta^2 = 0` is allowed in the book).

---

## 3. Stout (1970), Theorem 1, and Stout (1974), Theorem 5.4.1

### 3.1 Restatements read (with type)

**T1. RESTATEMENT of Stout's Theorem in the form the task describes** (transcribed from the rendered page; the PDF text layer drops all formulas). B. O. Osu and P. U. Uzoma, "The Hartman-Wintner law of the iterated logarithm for noncommutative martingales",
Int. J. Math. Res. 5(2) (2016) 123-130, p. 127 (`archive.conscientiabeam.com/index.php/24/article/download/2190/3209/3122`); their reference [14] is Stout, Z. Wahrsch. verw. Gebiete 15, 279-290, 1970.

> "According to Stout [14] if (X_i, F_i, i >= 1) is a martingale difference sequence with S_n^2 = sum_{i=1}^n E[X_i^2 / F_{i-1}] -> infinity, a.s, U_n = (2 log log S_n^2)^{1/2}, F_{i-1} measurable random variables L_i -> 0 a.s., and |X_i| <= L_i S_i / u_i a.s. for all i >= 1. Then limsup_{n->infinity} sum_{i=1}^n X_i / (S_n U_n) = 1 a.s."

(Typographical blemishes in the source: "S_i/u_i" for `S_i/U_i`, "= i >= 1". The data match the task statement: `s_n^2 -> infinity` a.s.; predictable `K_n = L_n -> 0` a.s.; `u_n = (2 log log s_n^2)^{1/2}`; bound for all `i >= 1`; conclusion `limsup = 1`.) This is a low-prestige journal; treat as a transcription that agrees with independent sources on the shape, not as proof of the hypothesis wording.

**T2. RESTATEMENT of the upper half, attributed to "Stout (1970, 1973)".** de la Pena, Klass and Lai, "Pseudo-maximization and self-normalized processes", Probability Surveys 4 (2007) 172-192 (arXiv:0709.2233), Theorem 3.1, p. 184 (read from the rendered page):

> "A well-known result in martingale theory is Stout's (1970, 1973) LIL that uses the square root of the conditional variance for normalization.
> Theorem 3.1. Let {d_n, F_n}, n = 1, ... be an adapted sequence with E(d_n | F_{n-1}) <= 0. Set M_n = sum_{i=1}^n d_i, sigma_n^2 = sum_{i=1}^n E(d_i^2 | F_{i-1}). Assume that (i) d_n <= m_n for F_{n-1}-measurable m_n >= 0, (ii) sigma_n^2 < infinity a.s. for all n, (iii) lim_{n->infinity} sigma_n^2 = infinity a.s., (iv) limsup_{n->infinity} m_n sqrt(log log(sigma_n^2)) / sigma_n = 0 a.s. Then limsup M_n / sqrt(2 sigma_n^2 log log sigma_n) <= 1 a.s."
(printed as stated, with `log log sigma_n` in the final denominator). Here the pairing is `m_n` (predictable) with `sigma_n` (which includes the `n`-th conditional variance): the same pairing as in T1 and in the Lean Prop.

**T3. SECONDARY discussion of the hypothesis and of the two halves.** de la Pena, Klass, Lai, Ann. Probab. 32 (2004) 1902-1933 (arXiv:math/0410102), Section 6 (their own Theorem 6.1 is a self-normalised analogue; quoted as printed):

> "Theorem 6.1. Let {X_n} be a martingale difference sequence with respect to an increasing sequence of sigma-fields F_n such that |X_n| <= m_n a.s. for some F_{n-1}-measurable random variable m_n, with V_n -> infinity and m_n / {V_n (log log V_n)^{-1/2}} -> 0 a.s. Then (1.9) holds."
> "... X_n is clearly bounded above and, therefore, satisfies the boundedness condition of Stout (1970). Note that Var(X_i) ~ 4 (log i)^3 / i and, therefore, s_n^2 := sum_{i=1}^n E(X_i^2 | F_{i-1}) ~ (log n)^4, yielding [S_n / (s_n (log log s_n)^{1/2}) -> 0] a.s., which is consistent with Stout's (1970) upper LIL."
and in the survey (T2 source): "m_n/sigma_n ~ 2 (log n)^{1/2} -> infinity and therefore one still does not have Stout's (1970) lower LIL in this example."
So Stout's paper contains an upper half and a lower half, with the boundedness condition being the predictable `m_n = o(s_n (log log s_n^2)^{-1/2})` type (this is also the "Stout-type" `F_{n-1}`-measurable bound used in T2).

**T4. RESTATEMENT with deterministic `alpha_n` and the `max{1, ln ln}` convention.** Zeng, "Kolmogorov's law of the iterated logarithm for noncommutative martingales", Ann. IHP 51 (2015) (arXiv:1212.1504), p. 1-2, and Panja-Ricard-Saha, "Non-commutative Law of iterated logarithm", arXiv:2509.22037, p. 1-2:

> "For any x > 0, we define the notation L(x) = max{1, ln ln x}." ... "Kolmogorov's LIL was generalized to martingales by Stout [15]. Let (X_n, F_n)_{n>=1} be a martingale with E(X_n) = 0. Let Y_n = X_n - X_{n-1} for n >= 1, X_0 = 0 be the associated martingale differences. Put s_n^2 = sum_{i=1}^n E[Y_i^2 | F_{i-1}]. Then Stout proved that if s_n^2 -> infinity and (1) holds, then limsup X_n / sqrt(s_n^2 L(s_n^2)) = sqrt 2 a.s."
> where (1) is "|Y_n| <= alpha_n s_n / sqrt(L(s_n^2)) a.s." "for some positive sequence (alpha_n) such that lim alpha_n = 0".
(Panja et al.: "If s_n^2 -> infinity a.s. and if for some sequence (alpha_n) of positive reals with alpha_n -> 0, |Y_n| <= alpha_n s_n / sqrt(L(s_n^2)) a.s., then limsup X_n / sqrt(s_n^2 L(s_n^2)) = sqrt 2 a.s."; `L(x) = max{1, ln ln x}` for `x > 1`.)
These state a deterministic `alpha_n`, which is a special case of T1's predictable `L_i`; they are written for the non-commutative setting where random `K_n` are unavailable, and they show the convention `ln ln` replaced by `max{1, ln ln}` for small `x`. Note `sqrt 2 * sqrt(s_n^2 L(s_n^2)) = s_n u_n` with `u_n = sqrt(2 L(s_n^2))`, so this is `limsup S_n/(s_n u_n) = 1`.

**T5. CITATION-ONLY.** Chatterji, Bull. AMS 80 (1974), p. 496: "a recent law of the iterated logarithm due to Stout [10] (which itself is a perfect generalization of the classical law of Kolmogorov [7] ...)". Sasai-Miyabe-Takemura (arXiv:1504.06398), Junge-Zeng and others cite the 1970 paper without a statement.
I found no restatement that carries both the exact Stout hypothesis wording and the convention for small `s_n^2`, and no restatement of Stout (1974), Theorem 5.4.1.

### 3.2 What is confirmed about the hypotheses (task list)

| Item | Status |
|---|---|
| `s_n^2 = sum_{i<=n} E(X_i^2 | F_{i-1}) -> infinity` a.s. | T1, T2 (iii), T4: confirmed |
| `|X_n| <= K_n s_n / u_n` a.s. with `K_n` `F_{n-1}`-measurable | T1 (`L_i`, verbatim), T2 (`m_n` `F_{n-1}`-measurable, one-sided), T3 (`m_n` `F_{n-1}`-measurable in the self-normalised analogue): confirmed by restatements; T4 gives only the deterministic special case. Stout's own wording not seen. |
| `K_n -> 0` a.s. | T1: confirmed. T2 (iv) and T3 give the equivalent form `m_n sqrt(log log s_n^2)/s_n -> 0` a.s. |
| `u_n = (2 log log s_n^2)^{1/2}` | T1 verbatim; T4 uses `L = max{1, ln ln}`; `sqrt 2 L^{1/2}` vs `(2 log log)^{1/2}` differ only by the convention for small `s_n^2` |
| Bound needed for all `n` or eventually | T1: "for all `i >= 1`" (literal, which forces a convention when `log log s_i^2` is undefined, i.e. `s_i^2 <= 1`). T2, T4: stated without quantifier (= for all `n`). Nothing states "eventually". |
| Convention when `log log s_n^2` is undefined | T4 only: `L(x) = max{1, ln ln x}`. T1 and T2 silent. Unresolved from primary text. |
| Conclusion | T1: `limsup S_n/(s_n u_n) = 1` a.s. (equivalently `sqrt 2` with `L`, T4). T2: `<= 1` for the upper half (supermartingale differences, one-sided `d_n <= m_n`). |
| Integrability | T1, T4: `E X_n = 0` (martingale), `s_n^2` finite a.s.; T2 (ii). No requirement `E S_n^2 < infinity` is visible; the Lean `MemLp 2` is stronger. |

### 3.3 Translation (Lean -> Stout)

`predBracket mu F S S n = sum_{t<n} mu[(S(t+1)-S t)^2 | F t] = sum_{i=1}^n E[X_i^2 | F_{i-1}] = s_n^2` with `X_i = S_i - S_{i-1}`: the Lean `n` is Stout's `n`, and `s_n^2` is `F_{n-1}`-measurable (each term is conditional on some `F t` with `t <= n-1`).
`B (n+1)` is `F n`-strongly measurable and bounds `|S(n+1) - S n| = |X_{n+1}|`; so `B n` (`n >= 1`) is `F_{n-1}`-measurable and bounds `|X_n|`, paired with `s_n`, as `K_n s_n/u_n` in T1.
Put `L_n := log log (max(s_n^2, e^e)) >= 1`, `u_n := sqrt(2 L_n)`, and
`K_n := B_n u_n / s_n` on `{s_n > 0}`, `K_n := 0` on `{s_n = 0}`.

* `K_n` is `F_{n-1}`-measurable (`B_n`, `s_n^2` are).
* `K_n = sqrt 2 * (Lean growth expression)` a.s. for large `n`, and the Lean growth hypothesis says that expression `-> 0` a.s.; hence `K_n -> 0` a.s.
* `|X_n| <= B_n = K_n s_n/u_n` a.s. on `{s_n > 0}` for every `n`; on `{s_n = 0}` (an `F_{n-1}`-event where `E[X_n^2 | F_{n-1}] = 0`) we have `X_n = 0` a.s., so the bound holds with `K_n = 0`.
* `s_n^2 -> infinity` a.s. is a Lean hypothesis; then `L_n = log log s_n^2` for all large `n`, so `u_n` agrees with Stout's `u_n` eventually, and any convention used by Stout for the finitely many small `n` is handled by redefining `K_n := B_n u_n^{Stout}/s_n` for those `n` (finitely many, it does not affect `K_n -> 0`).
* `B n` can be replaced by `|B n|` (or `max(B n, 0)`) if `K_n >= 0` is demanded: `B (n+1) >= |X_{n+1}| >= 0` a.s. for all `n` simultaneously.

Conclusion: Stout gives `limsup S_n/(s_n u_n) = 1` a.s. (here `S_n = sum_{i<=n} X_i` because `S 0 = 0`), and `s_n u_n = sqrt(2 s_n^2 log log s_n^2) > 0` for large `n`. For such `n`,
"`limsup = 1`" is equivalent to: for every `delta > 0` eventually `S_n <= (1+delta) sqrt(2 s_n^2 log log s_n^2)` and frequently `S_n >= (1-delta) sqrt(2 s_n^2 log log s_n^2)`. The Lean conclusion is exactly this (the `max` is absent in the conclusion but `s_n^2 > e^e` eventually, and both clauses are tail statements). The union over `delta = 1/k` is countable, so the `forall^m omega, forall delta` quantifier order is right.

### 3.4 Points where the Lean version is a stronger claim than the source (Lean hypotheses weaker than Stout's, as restated)

1. **Predictable random bound.** `B` is only `F_n`-strongly measurable (random). This matches T1 (`F_{i-1}`-measurable `L_i`) and T2/T3. It would be a stronger claim than Stout's if Stout's hypothesis were deterministic `alpha_n` (T4 wording). I judge T1-T3 to be the true wording (T4 is written for a setting without random `K_n`), but this is the **one unverified point** and it is the reason for "WITH-REMARK".
2. **`F_0` nontrivial and the start of the filtration.** Stout's `F_0` is presumably trivial (`E(X_1^2 | F_0) = E X_1^2`); Lean allows an arbitrary `F 0`. Standard remark: prepend a zero term (`X'_1 := 0` with `F'_0` trivial, `F'_1 := F_0`, `X'_{i+1} := X_i`, `F'_{i+1} := F_i`); then `s'_{n+1}^2 = s_n^2`, the predictable bound `K'_{n+2} := K_{n+1}` is `F'_{n+1} = F_n`-measurable, and `limsup` is unchanged. Costs nothing.
3. **Convention for small `s_n^2`.** Lean uses `max(., e^e)` inside `log log` in the growth hypothesis and no `max` in the conclusion. This is not a weakening of Stout: hypotheses are asymptotic, and the growth hypothesis (Lean) and `K_n -> 0` (Stout) coincide for large `n`; see 3.3. (Same convention as T4, since `ln ln(x v e^e) = max{1, ln ln x}` for `x > 1`.)
4. `B 0` appears in the Lean growth hypothesis but has no bound attached. Only an initial term of a limit; irrelevant.

### 3.5 Points where the Lean version is stronger than needed (Lean asks more; harmless)

* `forall n, MemLp (S n) 2 mu` (Stout needs at most `s_n^2 < infinity` a.s.) and `S 0 = 0` everywhere.
* The bound `|S(n+1) - S n| <= B(n+1)` is demanded for **all** `n` a.s. (if Stout needs it only eventually, this is more than needed; T1 says all `i >= 1`).
* `Martingale` (equality) is used for the whole statement; only the lower half needs two-sided control, the upper half holds for supermartingale differences (T2), but the Prop asks for both halves.
* `Tendsto (predBracket) atTop atTop` a.s. and the growth hypothesis are a.s. statements with no separate requirement `K_n >= 0`; both are implied by, and imply, the source's versions as in 3.3.
* Conclusion: equivalent to `limsup = 1` (not stronger, not weaker).

**Verdict: IMPLIED-WITH-REMARK** (remark: `K_n := B_n u_n/s_n`, prepending a zero term for `F_0`, finitely many initial indices; all conditional on Stout's hypothesis being the predictable-`K_n` form of T1-T3).
Fix if not: if Stout requires deterministic `alpha_n`, replace `B : N -> Omega -> R` by a deterministic `b : N -> R` (constant in `omega`) in `StoutLIL`, or (better) cite the predictable form from a source that states it (for the upper half de la Pena-Klass-Lai, arXiv:0709.2233 Thm 3.1, Stout 1973; for the lower half Stout 1970 is needed).

---

## 4. Consumption notes (from `draft-audit-1.md`, not re-checked)

The earlier audit records that the consumers (paper lines 1401, 1412, 1521, 1647) use predictable `B_n = C|X_{n-1}|` for the bracket-based LIL, and constant bounds otherwise; the Lean Prop needs the predictable form for the first of these, so the confirmation of T1-T3 matters. The CLT is used with `F_{n,i} = F_i` and constant `v`, possibly `v = 0` (line 1521); this is the `v = 0` case covered by 2.4.

## 5. What would close the remaining gaps

1. Read Hall-Heyde p. 58-59 (Theorem 3.2, Corollary 3.1 and the Remarks on (3.21)/constant `eta^2`/`eta^2 > 0`).
2. Read Stout (1970), Theorem 1 and its convention for small `s_n^2`, or Stout (1974), Theorem 5.4.1 (archive.org `almostsureconver0000stou` is borrowable with an account; Springer `10.1007/BF00533299`).
3. Nothing else is open: the Lean-to-source reductions in 2.3, 2.4 and 3.3 do not depend on the wording of the conventions.

## Addendum: sources retrieved for the form of `StoutLIL`

The open question was whether Stout's theorem allows the bound on the increments to be
predictable and random, as `StoutLIL` does (`B (n+1)` is `ℱ n`-measurable, and
`B n · √(log log s_n²) / s_n → 0` almost surely), or only deterministic. Retrieved since:

* **Upper half: confirmed.** de la Peña, Klass and Lai, *Pseudo-maximization and self-normalized
  processes*, Probab. Surveys 4 (2007), arXiv:0709.2233, Theorem 3.1, attributed to Stout (1970,
  1973). It assumes `d_n ≤ m_n` for an `F_{n-1}`-measurable `m_n ≥ 0`, `σ_n² → ∞` a.s. and
  `lim sup m_n √(log log σ_n²) / σ_n = 0` a.s., and concludes `lim sup M_n / √(2σ_n² log log σ_n²) ≤ 1`
  a.s. With `m_n := B n`, this implies the first conjunct of `StoutLIL` (the `∀ᶠ` upper bound).
* **Lower half: not confirmed.** The two restatements of Stout (1970) retrieved both use a
  deterministic sequence `(α_n)` of positive reals with `α_n → 0` and `|Y_n| ≤ α_n s_n / √L(s_n²)`:
  * Zeng, Ann. Inst. H. Poincaré Probab. Statist. 51 (2015), arXiv:1212.1504, introduction;
  * Panja, Ricard and Saha, arXiv:2509.22037v2, (1.1).

  Neither restatement says the deterministic form is Stout's full generality. The deterministic form
  is strictly weaker than the second conjunct of `StoutLIL` (the `∃ᶠ` lower bound). Hall–Heyde
  Theorem 4.8 and Stout (1974) Theorem 5.4.1, which would settle it, are still unread.
* **Verdict:** the CONCERN is narrowed to the lower conjunct of `StoutLIL`, and it stays open for the
  author. The check is to read Hall–Heyde (1980) Theorem 4.8 or Stout (1970) Theorem 1 and confirm
  that `K_n` may be `F_{n-1}`-measurable.
