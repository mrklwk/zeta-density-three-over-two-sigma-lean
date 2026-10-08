# Comparison of leading zero-density exponents

Write the bound as $N(\sigma,T)\ll T^{A(\sigma)(1-\sigma)+\varepsilon}$.
This formalization supplies $A(\sigma)=3/(2\sigma)$ for $3/4<\sigma<1$.
Positive-height and symmetric-height counts have the same leading exponent,
by conjugation; this repository uses the symmetric inclusive count.

The benchmark combines the post–Guth–Maynard bounds in
[Tao, Trudgian and Yang, Table 2, printed p.33](https://arxiv.org/pdf/2501.16779)
with the public preprint of
[Kerr, Theorem 6, printed p.7, equations (14)–(15)](https://arxiv.org/pdf/1909.12075).
Kerr supplies this same exponent for $\sigma\ge23/29$. His preprint is
included in the comparison, rather than omitted on publication-status grounds.

Compared with these estimates:

| Range | Leading-exponent comparison |
| --- | --- |
| $3/4<\sigma<23/29$ | Strictly smaller exponent here |
| $23/29\le\sigma\le7/8$ | Same best located leading exponent |
| $7/8<\sigma<1$ | Existing estimates are stronger |

Here $23/29=0.7931034483\ldots$. The assertion is a comparison with the cited
estimates, not an exhaustive priority claim about all unpublished work.
Equality of leading exponents does not compare constants or logarithmic losses.
The endpoint $\sigma=3/4$ is not included in the theorem.

For the Table 2 rows below $23/29$, subtracting $3/(2\sigma)$ from the listed
$A(\sigma)$ gives positive quantities. The respective numerators after
clearing positive denominators are $15\sigma-9$, $6-6\sigma$,
$9-9\sigma$, $3-3\sigma$, $18-23\sigma$, $3-3\sigma$, and
$24-30\sigma$. Each is positive on its stated row interval.
Kerr's other branch (Theorem 7) does not lower the comparison there: its
$36/(138\sigma-89)$ term already exceeds $3/(2\sigma)$ throughout that
branch's interval.

Above $7/8$, Heath-Brown's bound
$A(\sigma)\le\max\{3/(10\sigma-7),4/(4\sigma-1)\}$ already beats
$3/(2\sigma)$: the first term is smaller when $\sigma>7/8$, and the
second when $\sigma>3/4$. The [exponent database, Theorem 11.18 and
Proposition 11.37](https://teorth.github.io/expdb/blueprint/zero-density-chapter.html)
records this bound and the Kerr comparison.

If Kerr's preprint were excluded, the Table 2 comparison would instead extend
the strict-improvement endpoint to $1867/2347=0.7954835961\ldots$, where
Bourgain's equal-exponent range begins. That is not the primary comparison used
here. Separately, this exponent is below $2(1-\sigma)$ throughout $(3/4,1)$;
improvement over that density-hypothesis exponent is a different statement from
improvement over the cited literature.

## Analytic source

D. R. Heath-Brown, *The twelfth power moment of the Riemann zeta-function*,
Quarterly Journal of Mathematics 29 (1978), 443–462, provides the classical
moment and point/local-mean arguments. Relevant locations are Theorem 1
(p.444), Lemma 3 (p.455), and equation (44) (p.456).
[Primary scan](https://wiki.math.ntnu.no/_media/ma3001/2025h/analyticnumbertheory/heathbrowntwelfthmoment.pdf).
The formalized moment has an arbitrary positive power loss. The density proof
also needs its separately proved Type I large-values theorem; the moment alone
is not asserted to imply the full range here.
