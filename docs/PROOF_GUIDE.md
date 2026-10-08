# Structure of the proof

The proof has two analytic inputs: a large-values estimate and the critical-line
twelfth moment. A fixed-family zero detector connects them to actual zeta zeros.

## Large values

`MathCollab.Density.large_values` proves, for every $\kappa,\varepsilon>0$,
the existence of a positive constant $C$ such that

$$|W|\le C T^\varepsilon(N^2/V^2+N^3\sqrt T/V^4).$$

Its hypotheses are $T\ge2$, a positive integer $N$, $V>0$,
$T^{1/3}\le N\le T$, $V\ge N^{3/4+\kappa}$, and arbitrary complex
coefficients $|a_n|\le1$ on $N<n\le2N$. The finite set $W$ is 1-separated,
lies in an interval of length $T$ with arbitrary starting point, and satisfies

$$\left|\sum_{N<n\le2N}a_n\exp(it\log(n/N))\right|\ge V\quad(t\in W).$$

The constant precedes all $T,N,V,a,W$. There is no moment or zero-set premise.
[LargeValues.lean](../lean/MathCollab/Density/LargeValues.lean) exposes this
statement; its proof uses the auxiliary complete-pair energy, product grouping,
Poisson–Mellin reflection, a finite bootstrap supremum and uniform absorption.
The full-line reflection uses the all-frequency estimate

$$\left|\int_a^b z^{-1}e^{i(\tau\log z-2\pi z)}\,dz\right|
\le6/\sqrt{2\pi a}\qquad(0<a\le b,\ \tau\in\mathbb R).$$

## From detectors to zeros

Set $a=1/(2\sigma)$, $c=3/(4\sigma)$ and $p=3(1-\sigma)/(2\sigma)$.
The smooth mollifier detector covers every slab zero by a long smooth piece
or a short member of a fixed finite polynomial family. Coefficients are fixed
before the zero is chosen, and detection stays at its original ordinate.

Bounded powers put short pieces in $T^a\le L\le 2^K T^c$, with $K$ fixed
before $T$. The large-values estimate and the identities
$2(1-\sigma)c=1/2+(3-4\sigma)a=p$ give the short-count exponent.
Long pieces are bounded by a weighted actual critical-line mean and then the
twelfth moment. Since $c<1$, their exponent has a fixed saving.

Local multiplicity bounds restore all zeros after separated representatives
are counted. The short set and its complement partition the entire slab.
Dyadic summation, conjugation, and a bounded-height contribution give the
symmetric inclusive count for every $T\ge2$.

[ConditionalDensity.lean](../lean/MathCollab/Density/Stronger/ConditionalDensity.lean)
states the moment-to-density implication with its moment premise visible.
[NativeDensity.lean](../lean/MathCollab/Density/Stronger/NativeDensity.lean)
supplies the proved native moment, leaving no analytic premise in the final result.
