# Source for the predictable-bound lower half of Stout's martingale LIL

**Verdict: CONFIRMED-PREDICTABLE.** Stout's 1970 paper states the lower half as its own Theorem 2 (the
upper half is Theorem 1). Both theorems take K_n to be F_{n−1}-measurable. Cite the lower half as
**Stout (1970), Theorem 2**, not Theorem 1.

## 1. Primary source, read from the paper's own pages
W. F. Stout, "A Martingale Analogue of Kolmogorov's Law of the Iterated Logarithm",
Z. Wahrscheinlichkeitstheorie verw. Geb. 15 (1970) 279–290, doi:10.1007/BF00533299.
Open-access PDF: https://link.springer.com/content/pdf/10.1007/BF00533299.pdf
- **Setup, p. 279:**
  - "Let Y_n = X_n − X_{n−1} for n ≥ 1, X_0 = 0, F_0 = (φ, Ω), s_n² = Σ_{i=1}^n E[Y_i² | F_{i−1}],
    and u_n = (2 log_2 s_n²)^{1/2}."
  - "Relationships of equality or inequality stated between random variables are to be understood
    to hold only almost surely".
  - log_2 is the iterated logarithm; the proofs use s_{t_k} u_{t_k} ≈ (2p^{2k} log_2 p^{2k})^{1/2}.
- **Theorem 1, p. 286 (upper half):** "If s_n² → ∞ and |Y_n| ≤ K_n s_n/u_n for n ≥ 1 where K_n are
  F_{n−1} measurable with K_n → 0, then Lim sup X_n/(s_n u_n) ≤ 1."
- **Theorem 2, p. 287 (lower half):** "If s_n² → ∞ and |Y_n| ≤ K_n s_n/u_n for n ≥ 1 where K_n are
  F_{n−1} measurable with K_n → 0, then Lim sup X_n/(s_n u_n) ≥ 1."
- **Proof of Theorem 2, pp. 287–288:**
  - It truncates on C_n^M = {K_j ≤ M for all j ≤ n} and pads with independent symmetric ±1
    variables R_n.
  - It ends: "X_{t_k} > (1−δ') s_{t_k} u_{t_k} i.o. on ∩_n C_n^M and hence on ∪_M ∩_n C_n^M = Ω".
    This is the "infinitely often ≥ (1−δ) s_n u_n" form asked about.
- **Intent, p. 280:** "we strengthen the result slightly, even for the independent case, by requiring
  that the K_n be merely F_{n−1} measurable rather than constants."
- **Remark, p. 288:** "In prior versions of our results, K_n were constant. Dropping this restriction
  improved the utility of Theorems 1 and 2."
- **Measurability of K_n:** F_{n−1}-measurable. Lower half included: yes (Theorem 2).
- **Reading of the hypotheses:** by the p. 279 convention, s_n² → ∞ and K_n → 0 hold almost surely,
  and the bound |Y_n| ≤ K_n s_n/u_n holds almost surely for every n ≥ 1.
  - The paper requires the bound for every n ≥ 1, not just eventually. A formal statement with
    "eventually" needs the routine finite-modification reduction, which leaves the lim sup unchanged
    because s_n u_n → ∞.
  - u_n is real only once s_n² > e; the paper does not address small n.

## 2. Secondary restatements (corroboration only; all predictable, all two-sided "= 1")
- Dhillon, Ghosh, Kataria, "On Elephant Random Walk with Delayed Amnesia", arXiv:2606.21111v2
  (2026), https://arxiv.org/abs/2606.21111, Theorem 2.3: "(Stout (1970), Theorem 1, Theorem 2). If
  lim_{n→∞} t_n²=∞ a.s. and |ΔM_n| ≤ K_n t_n/u_n, n≥1 for some K_n that is F_{n−1}-measurable such
  that lim_{n→∞} K_n=0 a.s. then limsup_{n→∞} M_n/(t_n u_n)=1 a.s." (t_n², u_n as in Stout.)
- Coletti, de Lima, Gava, Luiz, arXiv:2005.07288v4 (2021), proof of Thm 6: "follows from a
  application of Theorems 1 and 2 of [24]. … It is clear that K_n is F_{n−1} measurable." ([24] is
  Stout 1970.) This applies the theorems to get a lim sup equality, i.e. it uses the lower half.
- Osu, Uzoma, Int. J. Math. Res. 5(2) (2016) 123–130, p. 127 (minor venue; typos are the paper's):
  "According to Stout [14] if (X_i, F_i, ≥1) is a martingale difference sequence with S_n² →∞, a.s,
  … F_{i−1} measurable random variables L_i → 0 a.s., and |X_i| ≤ L_i S_i/u_i a.s ∀ i≥1. Then
  lim sup Σ_{i=1}^n X_i/(S_n U_n) = 1 a.s."
  https://archive.conscientiabeam.com/index.php/24/article/download/2190/3209/3122

## 3. Related, other, and inaccessible
- Related, not Stout's statement: de la Peña–Klass–Lai, Ann. Probab. 32(3A) (2004) Thm 6.1
  (arXiv:math/0410102) is a lower-half LIL with F_{n−1}-measurable m_n, normed by V_n² = ΣX_i².
- Deterministic or paraphrase only: Passenbrunner arXiv:2409.13227 (uniform |ΔM_n| ≤ L); Zeng,
  Ann. IHP 51 (2015) (constant α_n); Hall–Heyde, Bull. Austral. Math. Soc. 14 (1976) (no statement).
- Not open access: Hall–Heyde (1980) Thm 4.7/4.8; Stout (1974) Thm 5.4.1; Chen–Guo (1991). Behind a
  bot check (not circumvented): Project Euclid (Fisher 1992, Freedman 1975, Lai–Wei 1982,
  Heyde–Scott 1973), Google Books, zbMATH reviews, Pelletier SPA 78 (1998) "Result 1".
