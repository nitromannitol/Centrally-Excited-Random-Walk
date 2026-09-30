# Proof audit of the three supplied OERW drafts

Audit date: 8 September 2026. This is an internal mathematical consistency review, not external peer review.

## Scope and theorem statements

The supplied proofs support a manuscript about **origin-excited / centrally excited random walk with constant Euclidean inward first-departure mean**. Take

\[
q_x(\pm e_i)=\frac1{2d}\mp\frac\varepsilon2\frac{x_i}{|x|},\qquad 0<\varepsilon<1/d,
\]

on the first departure from a nonzero site, and simple random walk thereafter and at the origin. The restriction on epsilon is sufficient for strict positivity of these canonical probabilities. Angularly varying radial strengths, such as a mean proportional to \(-x/\|x\|_1\), are not covered by the asserted Euclidean ball limit with this radius.

The dimension scope must be **every fixed integer d >= 2**. The arguments do not give d = 1. In dimension one, the first-cookie compensator is proportional to the two extrema, and diffusive martingale fluctuations are of the same scale as the proposed radius. One must not append a deterministic interval limit in dimension one by formally substituting d = 1 in the radius formula. The title or introduction should make the d >= 2 scope explicit even if informal discussion says "all dimensions."

There is a short contradiction to a deterministic compact interval shape in d = 1. Write the departure range as \([-L_n,R_n]\cap\mathbb Z\). The process \(Z_n=X_n+\varepsilon(R_n-L_n)\) is a bounded-increment martingale with predictable bracket \(n-\varepsilon^2(|A_n|-1)\). If the scaled extrema converged to finite deterministic numbers \(L_n/\sqrt n\to\ell\) and \(R_n/\sqrt n\to r\), then the martingale central limit theorem would give \(Z_n/\sqrt n\Rightarrow\mathcal N(0,1)\), since \(|A_n|=O(\sqrt n)\). Consequently \(X_n/\sqrt n\Rightarrow\mathcal N(-\varepsilon(r-\ell),1)\). This contradicts confinement of \(X_n/\sqrt n\) to a fixed bounded interval up to an error tending to zero. Thus excluding d = 1 reflects the behavior of the model, not merely a limitation of the supplied proof method.

Let \(N=n^{1/(d+1)}\), \(L=\log(n+2)\), \(c_0=2d\varepsilon\), and

\[
a=\left(\frac{d+1}{2d\varepsilon\omega_d}\right)^{1/(d+1)}.
\]

The first theorem can give the almost-sure ball sandwich, uniform cone local-time profile \(N^{-1}\ell_n(x)\to c_0(a-|x|/N)_+\), range asymptotic \(|A_n|/N^d\to\omega_da^d\), and fixed-site local-time asymptotic \(\ell_n(x)\sim c_0aN\). The last assertion gives recurrence at every fixed site.

The second theorem can use

\[
Q=\begin{cases}(L/N)^{1/2}&d=2,\\(L/N)^{d/(2d-1)}&d\ge3,\end{cases}
\qquad W=NQ^{1/d}.
\]

With probability at least \(1-Cn^{-p}\), it gives inner deficit at most \(CNQ\), outer excess at most \(CWL\), normalized local-time error at most \(CQ^{1/d}\), and normalized symmetric-difference volume at most \(CQ\). These bounds also hold eventually almost surely, with deterministic constants and a finite random threshold. They are upper bounds only; none of the drafts proves matching fluctuation lower bounds or optimality.

## Important source mismatch and its repair

The supplied planar source `oerw_radius_one_third (1).tex` proves only

\[
H_n\le Cn^{1/3}L^4,
\]

and explicitly disclaims a logarithm-free radius bound and a limit shape. The fluctuation source invokes a preceding planar ball-shape note and the stronger bound \(H_n\le CN\). That preceding planar shape note was not among the three supplied files. Therefore copying the fluctuation proof without an additional argument would leave a missing input.

The gap can be filled within the manuscript by extending the higher-dimensional coarse proof to d = 2, using the **exact planar potential kernel** in its truncated radial test. This also removes the unnecessary planar bulk discretization error from the fluctuation draft.

Write \(b_2=a_2\) for the planar potential kernel and \(b_d=-G_d\) for d >= 3, so \((P-I)b_d=\mathbf1_{\{0\}}\). Define

\[
\kappa_2(r)=\frac2\pi\log r+c_{\rm pot},\qquad
\kappa_d(r)=-\frac{2}{(d-2)\omega_d}r^{2-d}\quad(d\ge3),
\qquad \phi_r(x)=(b_d(x)-\kappa_d(r))_+.
\]

The standard asymptotics imply, for sufficiently large deterministic r,

\[
\phi_r(x)=0\quad(|x|\le r-1),\qquad
\phi_r(x)=b_d(x)-\kappa_d(r)\quad(|x|\ge r+1).
\]

For d = 2 this follows because the leading change in \((2/\pi)\log(r\pm1)\) is of order \(r^{-1}\), whereas the potential-kernel remainder is \(O(r^{-2})\). Finitely many inner sites are covered by \(\kappa_2(r)\to\infty\). The higher-dimensional argument is already in the supplied draft.

Consequently the test is exactly simple-random-walk harmonic beyond a fixed-width shell, its increments are bounded by \(Cr^{1-d}\), and its outward centered gradient satisfies \(u_x\cdot D\phi_r(x)\ge c|x|^{1-d}\) outside that shell. These facts yield in **every d >= 2**, without a bulk-error term,

\[
F(r+b_d)\le C M_{\rm sh}(r)\{F(r-b_d)-F(r+b_d)\}
+C\{\sqrt{M_n r^{1-d}F(r-b_d)L}+r^{1-d}L\}.
\]

Here the padding integer should have a different symbol from the potential kernel in the actual manuscript to avoid a notation collision.

## Unified coarse proof checks

The local-time lemma has the following dimension-dependent logarithms:

\[
M_{s,t}\le C\varepsilon k_{s,t}^{1/d}+\begin{cases}CL^2&d=2,\\CL&d\ge3,\end{cases}
\]

and the continuum approximation error can be taken as

\[
\delta=\begin{cases}C\sqrt{M_n}L&d=2,\\C(\sqrt{M_nL}+L)&d\ge3.\end{cases}
\]

The potential is correctly normalized as

\[
U_D(y)=\frac{2\varepsilon}{\omega_d}\int_D u_v\cdot\frac{v-y}{|v-y|^d}\,dv,
\]

and the spherical mean is \(2d\varepsilon F(r)\). In particular \(U_{B(0,b)}(y)=2d\varepsilon(b-|y|)_+\). The mass identity over a ball containing D is \(\int U_D=2\varepsilon\int_D|v|\), not a multiple with an additional d factor.

Set \(s=R_n^{1/d}\), \(\alpha=1/(2d-1)\), and \(\beta=(d-1)/(2d-1)\). The Holder estimate and spherical-cap argument give

\[
M_{\rm sh}(r)\le CB^\beta s^{1-\alpha}(F(r-b_d)+\delta)^\alpha
\]

on \([s,Bs]\), with the leading C independent of B. The cost of halving from A to the floor \(Cs^{2-d}L\) is bounded by

\[
CB^\beta s^{1-\alpha}A^\alpha
+C_Bs^{1-\alpha}\delta^\alpha L+CL.
\]

The remainder is \(O_B(s^{1-\alpha/2}L^{1+\alpha})\) in d = 2, and \(O_B(s^{1-\alpha/2}L^{1+\alpha/2})\) in higher dimensions. Both are o(s), because the local-time/range inequality first gives \(s\ge cn^{1/(d+1)}\).

At the resulting tail floor, any outward cap crossing uses at most \(CsL\) departure sites. The interval crossing inequalities are

\[
h^2\le C_\kappa\begin{cases}m^{4/3}L^{4/3}+mL^3&d=2,\\m^{2d/(2d-1)}L^{2d/(2d-1)}+mL^2&d\ge3.\end{cases}
\]

With h of order s, both right sides are o(s squared). This proves \(H_n\le Cs\). Integration of the potential approximation now gives an error \(s^d\delta=o(s^{d+1})\), which closes \(R_n\le CN^d\) and thus \(H_n,M_n\le CN\). This is a noncircular repair of the missing planar coarse input.

## Quantitative proof checks

The following steps of `oerw_fluctuations_and_rotor_transfer.tex` were checked and are consistent once the coarse input above is supplied:

1. At a closest unoccupied cell, with centered cell-set inradius b and excess E of volume m, the kernel is positive on E and gives \(U_D(y_0)\ge cm/N^{d-1}\). The contact-cell replacement costs only O(L).
2. The excess potential bound \(\|U_E\|_\infty\le Cm^{1/d}\) holds without any shape assumptions on E.
3. In d >= 3, the summable bracket kernel and a resolvent inequality give \(\ell_n(y)\le C((b-|y|)_++m^{1/d}+L)\). Its first moment is O(L) in d = 3 and bounded in d >= 4. At the contact cell this gives \(B_z\le C(m^{1/d}+L)\), hence \(m\le CN^dQ\).
4. In d = 2, the first contact estimate gives \(m\le CN^{3/2}L\). This improves the contact bracket to \(B_z\le CN\), and a second contact estimate gives \(m\le CN^{3/2}\sqrt L\), as claimed.
5. The exact quadratic identity is \(|X_n|^2=n-2\varepsilon\sum_{x\in A_n}|x|+\mathcal Q_n\). A martingale stopped at a deterministic coarse ball gives \(|\mathcal Q_n|\le C(N\sqrt{nL}+NL)\). Together with the cell replacement and excess bound, it yields \(|b/N-a|\le CQ\).
6. The shell local-time envelope is O(W) outside the inball. Tail halving costs O(WL), reaching \(F\le CN^{2-d}L\). A subsequent cap crossing would use O(NL) sites and contradict the crossing inequality. This proves the asserted outer error, including the final endpoint that may not yet have a departure.
7. The planar normalized Hausdorff exponent is \(n^{-1/12}L^{5/4}\). For d >= 3 it is \(n^{-1/((d+1)(2d-1))}L^{2d/(2d-1)}\). The physical outer error is obtained by multiplying by N.

All concentration statements must be proved simultaneously over deterministic targets, intervals, integer radii, and dyadic variance caps **before** the final range, contact cell, crossing direction, and last-entrance interval are selected. The sources handle this correctly; the consolidation should retain that point. A path-chosen projection is controlled by a vector martingale estimate derived from coordinate bounds.

Since the quantitative proof directly implies the shape theorem, the compactness/energy-rigidity argument in the higher-dimensional draft is optional. Its normalization, PDE sign, and energy identity are consistent, but including both full arguments would lengthen the manuscript without being necessary for the stated theorems.

## Rotor discussion

The rotor-transfer section is separate from the OERW theorem and explicitly leaves an additional radial-alignment assertion unproved. It should not be used to state a rotor disk theorem. A short related-model discussion is enough for the OERW manuscript; retain the supplied rotor calculations only if their conditional status is clear.

## Verification boundary

This audit checks the supplied mathematical arguments and the proposed planar repair. It does not certify a new theorem by external review. Bibliographic claims and publication status should be checked independently against primary sources; this audit did not rely on the supplied literature prose as verified evidence.

## Consolidated manuscript review

Read `cerw.tex` and `sections/local-times.tex`, `sections/coarse-radius.tex`, and `sections/fluctuations.tex` after their first complete assembly. The unified planar radial argument and the quantitative argument agree with the checks above. The review identified a source-transformation error replacing the exact cone coefficient `c_0` by generic `c` in the fluctuation section, including the mass normalization and the equation defining the radius. The exact coefficient must remain `c_0 = 2d epsilon`. The same source transformation corrupted `\left` into `\leqft`, a LaTeX error. Both were reported for immediate correction.

Additional precision corrections requested were an explicit deterministic containing ball with radius constant larger than a, a canonical shell padding depending only on d, an explicit interval `s <= j < tau` for crossing departures, restriction of shell-cap spheres to the approximation region, and explicit dimension assumptions at the two variance subsections. These do not alter the estimates. Follow-up reads confirmed restoration of the exact coefficient and `\left` commands, and all the listed precision corrections.

The final mathematical recheck covered the exact radius and cone constants, the two fluctuation scales, and every stated theorem, proposition, and lemma's dimension, time, probability exponent, and constant dependencies. The assembled manuscript supplies the missing planar coarse estimate, so its quantitative argument no longer relies on an absent source note. The final requested wording improvement is to stop the quadratic martingale on exiting the already chosen ball `B(0,KN)`, with its strict margin beyond the coarse radius, rather than an unspecified ball referred to by the coarse inequality. The same ball contains the support of both the local time and the comparison cone. This is a precision change and does not change the concentration estimate.

**Audit outcome:** no unresolved substantive mathematical gap was found in the assembled proof after these corrections. Display punctuation, typography, page layout, and bibliography verification remain part of the separate editorial/build review. This outcome is an internal consistency check, with the verification boundary stated above.
