---
title: "Reading guide: Natural boundaries of prime-pair Dirichlet series"
subtitle: "A section-by-section companion for the author"
author: "For the author"
date: "24 November 2026, for the paper as posted"
toc: true
toc-depth: 2
mainfontoptions:
  - "Renderer=HarfBuzz"
  - "BoldFont=STIX Two Text"
  - '`BoldFeatures={Weight=700}`{=latex}'
  - "BoldItalicFont=STIX Two Text Italic"
  - '`BoldItalicFeatures={Weight=700}`{=latex}'
monofont: "Latin Modern Mono"
monofontoptions:
  - "Scale=0.85"
  - "BoldFont=Latin Modern Mono"
monofontfallback:
  - "STIX Two Math:mode=harf"
  - "STIX Two Text:mode=harf"
  - "Arial:mode=harf"
---

# How to use this guide

Keep the paper beside this guide. Read one numbered statement in the paper, then its subsection here. The guide assumes you have worked through the primer; where a step uses background, the guide names the primer topic by its heading ("see the primer, 'The Gamma function, the Beta kernel, and the $S$-kernel'") rather than reteaching it.

The paper has eleven numbered sections and an appendix, 36 numbered theorems, lemmas, propositions and corollaries plus one numbered remark at the end of Section 3, two tables, one figure, and equations numbered consecutively from (1) to (13). Statement numbers run within sections (Lemma 2.1, Theorem 3.3), and lemmas, theorems, propositions and corollaries share one counter. Several items are not numbered: the classical inputs (Z1) to (Z6), the kernel facts (K1) to (K3), the hypothesis $(\mathrm H_\infty)$, the display that defines $G_2$ and $G_{\log}$, and the displayed formulas of Section 9 and inside proofs. Every number cited here was read from the paper's source.

Each subsection opens with a paraphrase beginning "The paper ...". What follows it is guide commentary: the steps the paper leaves out, worked small cases, and the reason the step is there. It does not change the paper; the paper is the source of truth.

The paper reuses some letters. Keep them apart:

- $G$ is the first series, $G_2$ the series over $p^2+q^2$, and $G_{\log}$ the series with the weight $\log q$; $\Gamma$ is the Gamma function; $\Gamma_0$, $\Gamma_{\mathrm{out}}$ (Sections 5 and 6) are contours, called graphs.
- $H$ is a height cutoff in Section 3 ($H=2\log X$), and a holomorphic remainder in Sections 6 and 7 ($D^\kappa=\operatorname{Log}_\kappa(v-x)X_x+H$).
- $X$ is a large parameter in Section 3; $X_x(v)$, with a subscript point $x$, is the coefficient function of equation (6); $Y_x(s)$ is its counterpart for $G_{\log}$ (Theorem 9.7), a different function that need not vanish at $x$.
- $\Theta_G$, $\Theta_S$ (Theorem 3.1) and $\Theta_2$ (Lemma 9.2) are the three sums over pairs, one per kernel.
- $B$ is the supremum of the real parts of the zeros; $\mathrm B(a,b)$, upright, is the Beta function; $B_\infty$ is the eventual supremum.
- $\mathcal C_G$, $\mathcal C_S$, $\mathcal C_2$ are the catalogues of candidate points (the bare $\mathcal C$ of Section 10 is $\mathcal C_G$ written out under RH); the bare $C$ of Section 7 is a complex constant, introduced in the paragraph before Theorem 7.4 and used there; $C$, $C_1$, $C(\varepsilon)$ elsewhere are unnamed constants.
- $\kappa$ is a real slope, and $e=(1+i\kappa)/|1+i\kappa|$ is the unit complex number giving the direction; $K$ is the kernel function $\Gamma(w)\Gamma(2-w)$ of $S$, and $\mathcal K$ is the kernel of either series in the variable $z$.
- $c(a)$ is a finite rational weighted sum attached to a point $a$ (equation (2)); it is minus the residue of $Q$ there.

Section 11 describes the tagged PrimePairNB release and the steps that join it to Alpöge's separate Lean proof of RH. Appendix A prints the main formal definitions and boundary declarations. [PrimePairNB v1.2.1](https://github.com/lpkralv/prime-pair-natural-boundaries/tree/v1.2.1)

## The proof in one page

Five series over pairs of primes, $G$, $T$, $S$, $G_2$ and $G_{\log}$, are each written as a contour integral of a product of two copies of the prime zeta function $P(z)=\sum_p p^{-z}$ (or of its negative derivative $Q=-P'$: both copies for $T$, one for $G_{\log}$), against a kernel built from Gamma functions. The candidate singular points of $P$ and $Q$ form a set $\Sigma$: the point $1$, the zeros $\rho$ of $\zeta$, and their scaled copies $\rho/k$ and $1/k$ with $k$ squarefree. In the variable $v$ (with $v=s$ for $G$, $T$ and $G_{\log}$; $v=2s+1$ for $S$, so $s=(a+b-1)/2$; and $v=2s$ for $G_2$, so $s=(a+b)/2$), a singularity of the series inside the half-plane where it is continued can only sit at a sum $a+b$ of two points of $\Sigma$. These sums are the candidate points; the statement is about the interior, not about the boundary line.

Corollary 1.4 gives the unconditional conclusions, including the boundaries of all five series. The paper proves the boundary implications under a hypothesis $(\mathrm H_\infty)$ that RH implies and that allows exceptions to RH. If that proof were withdrawn, Theorems 1.1–1.3 would still stand under $(\mathrm H_\infty)$ and Theorem 10.1 under RH. Genuine singularities of the series accumulate at every point of the boundary line from the right, and this blocks every continuation across it. There are two jobs, and a third step that redoes one of them for each new series.

1. Arithmetic (Section 3). At a point $x=a+b$ several pairs may contribute, and their contributions might cancel. The paper picks points $x=1+\rho/q$ ($\rho$ a zero on the critical line, $q$ a large prime) where the two ordered main pairs $(1,\rho/q)$ and $(\rho/q,1)$ together dominate the extra pairs. Counting gives many points where $\rho/q$ has a single representation, so the prime-zeta coefficient has size at least $1/q$ and the combined main contribution has a corresponding lower bound. The proof discards the few chosen points with an extra pair of low height. The exponential decay of the kernels bounds the total contribution of the remaining extra pairs. Theorem 3.1 gives a nonzero sum at points accumulating at every point of the line. In the open continuation half-plane the catalogue is discrete.
2. Analysis (Sections 4 to 8). For $T$ the integrand is meromorphic and a contour shift gives poles with residues equal to that sum (Section 4). For $G$ and $S$ the integrand has logarithmic singularities, so the series is multivalued. The paper cuts the plane along parallel rays in a fixed direction $\kappa$, gets a single-valued "sheet" $D^\kappa$ defined by one contour integral (Section 5), finds near each candidate point a logarithm times a coefficient function $X_x$ (Section 6), shows that rotating the direction or continuing along the paths of Theorem 7.4 changes the function only by things that do not alter that coefficient (Section 7), and concludes that no branch can extend meromorphically over a disc on the boundary line (Section 8).
3. Two more series (Section 9). Each changes one layer. $G_2$ has a new kernel with the same three properties, so the analysis is reused and the arithmetic is rerun for a new sum $\Theta_2$. $G_{\log}$ has one factor $Q$, so at a pinch a logarithm meets a pole; the local calculation becomes a residue (Lemma 6.2), the coefficient becomes a function $Y_x$ with $Y_x(x)=-\Theta_G(x)$, and the arithmetic of Section 3 is reused.

Section 10 uses RH to describe every catalogue point for $G$ and $T$. Section 11 and Appendix A explain the scope of the Lean implications and the written steps used in Corollary 1.4.

# 1. Abstract and Section 1: introduction

## The abstract

The paper defines five series summed over ordered pairs of primes,
$$G(s)=\sum_{p,q}(p+q)^{-s},\qquad T(s)=\sum_{p,q}\log p\log q\,(p+q)^{-s},\qquad S(s)=\sum_{p,q}p^{1-s}q^{2-s}(p^2+q^2)^{-2},$$
$$G_2(s)=\sum_{p,q}(p^2+q^2)^{-s},\qquad G_{\log}(s)=\sum_{p,q}\log q\,(p+q)^{-s},$$
and states the boundary implications under $(\mathrm H_\infty)$, the hypothesis that for every $\delta>0$ only finitely many zeros of $\zeta$ have real part above $\tfrac12+\delta$. The hypothesis follows from RH, allows zeros off the critical line, and puts no condition on the ordinates, the imaginary parts of the zeros. The abstract gives the boundary lines. The line $\operatorname{Re}s=1$ is a natural boundary for $T$, $G$ and $G_{\log}$, $\operatorname{Re}s=\tfrac12$ is one for $G_2$, and $\operatorname{Re}s=0$ is one for $S$. For the four multivalued series the conclusion holds on every branch.

Under the zero hypothesis several pairs of candidate singularities of $P$ can sum to one point. The arithmetic finds points where their contributions do not cancel and that accumulate at each point of the boundary line. In the region of continuation, a branch near a candidate collision is a logarithm times a holomorphic coefficient plus a holomorphic function on a small disc off a slit. Every branch reached along a path in the continuation region avoiding the candidate points has that same coefficient. Under the hypothesis the description applies to all branches based in the specified slit disc, including those reached by paths that met catalogue points on the way. The abstract ends by distinguishing the Lean implications from the unconditional conclusions of the written argument using Alpöge's certified Lean proof of RH. Section 11 gives the steps outside Lean.

What "natural boundary" means: a function defined on a half-plane has the line as a natural boundary when it cannot be continued analytically (or meromorphically) across any piece of the line, however small. The primer's topics "Natural boundaries: the single-valued case" and "Germs, analytic continuation along a path, and monodromy" give the definition and the standard picture: singularities that pile up densely along the line. "On every branch" is needed because $G$, $S$, $G_2$ and $G_{\log}$ are multivalued once continued (they contain logarithms), so one must say which of the many continuations is meant; the paper's answer is all of them.

The wording on the hypothesis describes what the proof uses. The finiteness condition would allow off-line zeros, even infinitely many, as long as for each positive margin only finitely many lie that far to the right of the critical line. Alpöge's theorem supplies RH itself, which discharges this hypothesis in Corollary 1.4. The difference matters in the arithmetic because the same proof works with competing pairs that full RH excludes.

## Section 1.1: series over pairs of primes

### Equation (1), the three starting series

The paper states $G$, $T$ and $S$ as equation (1). It says $G$ and $T$ are generating series of the Goldbach problem; that they converge absolutely for $\operatorname{Re}s>2$, while $S$ converges absolutely for $\operatorname{Re}s>\tfrac12$, with a two-line proof; that $S$ arises from the kernel $(1+x)^{-2}$ in place of $(1+x)^{-s}$ and is included to test the method on a different kernel (its summand is not symmetric in $p,q$, its kernel decays at half the rate of the kernel of $G$, and the kernel is holomorphic on the region the contour construction needs only for $s$ in a strip, which is the source of the constant $C$ in Section 7); and that each series is built from the prime zeta function $P(z)=\sum_p p^{-z}$ by a Mellin–Barnes integral, so its candidate singular points are $a+b$ (for $G$, $T$) or $(a+b-1)/2$ (for $S$), with $a$, $b$ candidate singular points of $P$. The sums run over ordered prime pairs. The logarithmic factors in $T$ replace both factors of $P$ in the integral by $Q=-P'$. The two different powers of $p$ and $q$ in $S$ are part of its definition, and its integral uses the variable $v=2s+1$. The convergence discussion gives the starting half-planes for these integrals.

One sentence in the first paragraph places the paper beside a current preprint. Li and Liu state that they derive the binary Goldbach conjecture for all sufficiently large even integers from the Generalized Riemann Hypothesis for Dirichlet $L$-functions together with either of two further spectral hypotheses (their Hypotheses S and R), each equivalent to a bound on the norm of a certain operator. The paper's point is the contrast: their results concern the number of representations of individual even integers, and this paper concerns the continuation of the generating series. It is not a proof of Goldbach under GRH alone, and the paper does not describe it as one.

The paper then introduces two further series in an unnumbered display,
$$G_2(s)=\sum_{p,q}\frac1{(p^2+q^2)^s},\qquad G_{\log}(s)=\sum_{p,q}\frac{\log q}{(p+q)^s},$$
absolutely convergent for $\operatorname{Re}s>1$ and $\operatorname{Re}s>2$. It says they probe the two places where the method could depend on the particular series: $G_2$ has a third kernel and its boundary on a different line, $\operatorname{Re}s=\tfrac12$; $G_{\log}$ carries the logarithmic weight on one prime only, so it lies between $G$ and $T$. Their candidate points are $(a+b)/2$ and $a+b$.

For $G_2$, the Mellin–Barnes kernel comes from applying the elementary kernel to $(p/q)^2$. The two factors still use $P$, so the new question is whether the arithmetic controls the sum with the new kernel weights. For $G_{\log}$, the kernel of $G$ stays in place and one factor becomes $Q=-P'$. The new local question is what happens when a logarithm meets a pole. Section 9 works out the two changes.

Why "generating series of the Goldbach problem": group the terms of $G$ by $n=p+q$. Then $G(s)=\sum_n r(n)n^{-s}$, where $r(n)$ is the number of ordered pairs of primes with $p+q=n$. Goldbach's conjecture says $r(n)>0$ for every even $n\ge4$. Likewise $T(s)=\sum_n r_\Lambda(n)n^{-s}$ with the weighted count $r_\Lambda(n)=\sum_{p+q=n}\log p\log q$. The paper does not attack Goldbach; it studies these Dirichlet series as functions of $s$.

Why $\operatorname{Re}s>2$: $r(n)\le n$, so $\sum_nr(n)n^{-\sigma}\le\sum_nn^{1-\sigma}$, which converges when $\sigma>2$. The bound loses only logarithms. By the prime number theorem the sum of $r(n)$ over a block $2^j\le n<2^{j+1}$ is of order $2^{2j}/j^2$ (at most the square of the number of primes below $2^{j+1}$, at least the square of the number in $(2^{j-1},2^j)$), which is the sense in which $n$ has on average about $n/\log^2n$ representations; so the series does not converge for any $\sigma<2$. The same holds for $G_{\log}$, whose weight $\log q$ is at most $\log n$.

Why $\operatorname{Re}s>\tfrac12$ for $S$, the paper's proof with the steps filled in. For $0\le t\le1$, $p^2+q^2\ge p^{2t}q^{2-2t}$: the weighted mean $tp^2+(1-t)q^2$ is at most $p^2+q^2$ and at least the weighted geometric mean $(p^2)^t(q^2)^{1-t}$. Raise to the power $-2$ and multiply by $|p^{1-s}q^{2-s}|=p^{1-\sigma}q^{2-\sigma}$: each term is at most $p^{1-\sigma-4t}q^{-2-\sigma+4t}$. The sum over pairs of such a product is $\bigl(\sum_pp^{1-\sigma-4t}\bigr)\bigl(\sum_qq^{-2-\sigma+4t}\bigr)$, and each factor converges when its exponent is below $-1$, that is when $4t>2-\sigma$ and $4t<1+\sigma$. The two conditions are compatible when $2-\sigma<1+\sigma$, that is $\sigma>\tfrac12$, and then some $t$ in $[0,1]$ satisfies both.

Why $\operatorname{Re}s>1$ for $G_2$: $p^2+q^2\ge pq$, so the sum is at most $\sum_{p,q}(pq)^{-\sigma}=P(\sigma)^2$, finite for $\sigma>1$.

Where the factor $(a+b-1)/2$ for $S$ comes from: the paper works with $v=2s+1$ for $S$ (Section 2.3), and singularities sit at $v=a+b$, that is $s=(a+b-1)/2$. For $G_2$ the variable is $v=2s$ (Section 9.1), which gives $(a+b)/2$.

The constant $C$ mentioned here is the complex constant introduced in the paragraph before Theorem 7.4 and used in that theorem. It appears for $S$ only. Read "holds only on a strip" as a statement about the sheets: the paper builds the sheets of $S$ on the strip $1<\operatorname{Re}v<3$, where (K1) holds on the whole range $0<\operatorname{Re}z<\operatorname{Re}v$. It is not a statement that the series or its Mellin–Barnes integral stops at $\operatorname{Re}v=3$. A path for $S$ can leave the strip to the right and come back, and on such an excursion the correction that a germ carries can pick up a constant (Theorem 7.4(b)).

## Section 1.1, continued: Landau and Walfisz

The paper says Landau and Walfisz proved that $\operatorname{Re}z=0$ is a natural boundary of $P$, that this says nothing directly about these series, and that the task is to show that at a dense set of candidate points the contributions of all pairs $(a,b)$ with $a+b$ equal to that point do not cancel.

The reason the boundary of $P$ does not pass to the series: a singularity of the series at $x$ is a sum of contributions from every pair $(a,b)$ of singular points with $a+b=x$. Two pairs could contribute equal and opposite amounts. So "the factors have singularities" does not imply "the product integral has a singularity". The whole of Section 3 is about ruling out that cancellation.

## Section 1.2: the hypothesis $(\mathrm H_\infty)$

The paper lets $\mathcal Z$ be the set of non-trivial zeros of $\zeta$, each counted once, and assumes

$(\mathrm H_\infty)$: for every $\delta>0$, only finitely many $\rho\in\mathcal Z$ have $\operatorname{Re}\rho>\tfrac12+\delta$.

It notes the equivalent form $B_\infty=\tfrac12$ (with $B_\infty$ as in Section 2), writes $B=\sup_\rho\operatorname{Re}\rho$ and LH for the Lindelöf hypothesis, and displays
$$\mathrm{RH}\Longrightarrow(\mathrm H_\infty)\Longrightarrow\mathrm{LH},\qquad(\mathrm H_\infty)\Longrightarrow B<1.$$
The first implication is immediate, and $(\mathrm H_\infty)$ follows already from the statement that only finitely many zeros lie off the critical line, so it allows exceptions to RH. The second follows from Backlund's criterion (Titchmarsh, Theorem 13.5). The third gives a zero-free half-plane, as Section 2 shows. The footnote reports the zero-free half-plane asserted by OpenAI, with $B\le7/8$, and the sharper one asserted by Liu, both in unrefereed 2026 preprints. The proof takes neither preprint as an input. In the notation of Bhowmik and Schlage-Puchta, the hypothesis says their abscissa $\sigma_0$ equals $\tfrac12$. It prescribes no rate for the approach of the real parts to $\tfrac12$.

The zero hypothesis is used at two strengths. The arithmetic in Section 3 and the corresponding argument for $G_2$ in Section 9.1 need only $B<1$, where $B$ is the supremum of the real parts of the non-trivial zeros. The analytic construction starts from the classical inputs. Its contour bounds depend on the locations of the zeros, and its domain is governed by $B_\infty$, the limiting supremum at large absolute height. In the collision variable $v$ the left edge is $\Re v=2B_\infty$. This gives a half-plane for four series and a strip for $S$. The condition $(\mathrm H_\infty)$ sets $2B_\infty=1$ and thereby places that edge on the boundary line in each series' own variable. The paper leaves open what continuation $B<1$ alone would give up to those lines.

On 20 November 2026 Alpöge announced a Lean proof of RH and of GRH for Dirichlet $L$-functions, in a library of about 17 million lines without an accompanying prose proof. The joint Lean and Mathlib statement, endorsed by the Lean FRO and the Mathlib Initiative on 21 November 2026, certifies the RH statement and proof. The joint statement reports that two independent tools confirmed that the theorem proved is exactly Mathlib's `RiemannHypothesis`. It also reports that Lean's official kernel checked the proof and that other checkers accepted it. The paper takes RH as proved on the strength of the cited certification and checks. The author read the headline statements and scanned the library's source, and relies on the cited checks for the build and proof.

Unpacking. Zeros come in the symmetric pattern $\rho$, $\bar\rho$, $1-\bar\rho$, $1-\rho$ about the critical line $\operatorname{Re}=\tfrac12$ (see the primer, "The classical inputs (Z1)–(Z6)"). RH says every zero is on the line. $(\mathrm H_\infty)$ allows zeros off the line, even infinitely many, but requires that the ones far up the strip crowd towards the line: for any margin $\delta$, all but finitely many sit within $\delta$ of it. Equivalently, the "eventual" supremum of the real parts, $B_\infty$ in Section 2.1, equals $\tfrac12$.

Why it implies $B<1$: for $\delta=\tfrac14$, only finitely many zeros have real part above $\tfrac34$. Each zero has real part strictly below $1$ (no zeros on $\operatorname{Re}=1$). A maximum over finitely many numbers each below $1$ is below $1$; together with the rest, which are at most $\tfrac34$, $B<1$. RH gives the stronger bound $B=\tfrac12$. The argument here explains why the proof can use a zero-free half-plane $\operatorname{Re}s>B$ even from the stated finiteness condition.

Backlund's criterion and Lindelöf: the Lindelöf hypothesis says $|\zeta(\tfrac12+it)|$ grows more slowly than any power $|t|^\varepsilon$. Backlund's criterion says it is equivalent to this: for every fixed $\sigma>\tfrac12$, the number of zeros with real part above $\sigma$ and height between $T$ and $T+1$ is $o(\log T)$ as $T\to\infty$. The fixed distance from the critical line is what makes $(\mathrm H_\infty)$ enough: only finitely many zeros have real part above $\sigma$, so that count is zero from some height on. This is how the global finiteness condition supplies the local count in Backlund's criterion. Alpöge’s certified Lean proof supplies RH, which implies both conclusions.

## Section 1.3: the theorems

### Theorem 1.1: the boundary for $T$

The paper proves, under $(\mathrm H_\infty)$, that $T$ has a single-valued meromorphic continuation to $\operatorname{Re}s>1$; that every disc $|s-(1+iy)|<\varepsilon$ centred on the line contains infinitely many poles of it; and consequently that no function meromorphic on a disc centred on the line agrees with it on the part of the disc in $\operatorname{Re}s>1$.

Why the "consequently" follows: suppose $g$ is meromorphic on the disc $D$ centred at $1+iy$ and agrees with $T$ on $D\cap\{\operatorname{Re}s>1\}$. Take a slightly smaller closed disc $D'$ with the same centre. A meromorphic function has only finitely many poles in a compact subset of its domain (poles are isolated, and an infinite set in a compact set accumulates). But $T$, and so $g$, has infinitely many poles in the half of $D'$ to the right of the line, by the first part with $\varepsilon$ the radius of $D'$. Contradiction. (Agreement off the poles forces the poles to be the same: near a pole of $T$, $g=T$ on a punctured neighbourhood, so $g$ is unbounded there too.)

Why $T$ is single-valued: it is built from $Q=-P'$, and differentiating $P$ removes its logarithms, leaving poles. Proved in Section 4.

### Admissible germs and the catalogue

The paper says $G$ and $S$ are built from $P$, which has logarithmic singularities, so they are not single-valued and need branches. It names the catalogue: a set of candidate points, closed and discrete under $(\mathrm H_\infty)$, $\mathcal C_G$ in $\operatorname{Re}s>1$ and $\mathcal C_S$ in $\operatorname{Re}s>0$ (defined in Section 2.4). A germ of $G$ at $s_1$ is admissible if it is reached from $\operatorname{Re}s>2$ by analytic continuation along a path in $\{\operatorname{Re}s>1\}\setminus\mathcal C_G$; a germ of $S$ at $s_1$ is admissible if it is reached from $\operatorname{Re}s>1$ along a path in $\{\operatorname{Re}s>0\}\setminus\mathcal C_S$ along which continuation exists. A germ extends meromorphically to an open set $W\ni s_1$ if some function meromorphic on $W$ agrees with it near $s_1$.

New words. A germ at $s_1$ is a convergent power series around $s_1$: the local value of a function, forgetting how large its disc is. Analytic continuation along a path carries a germ forward along a path by a chain of overlapping discs (see the primer, "Germs, analytic continuation along a path, and monodromy"). Different paths around a singular point can give different germs at the same endpoint; those are the branches. For $\log z$, going once counterclockwise round $0$ adds $2\pi i$.

"Closed and discrete": no two catalogue points accumulate inside the open half-plane. They may accumulate at the boundary line, and they do.

Note the asymmetry between $G$ and $S$ in the definition. Under $(\mathrm H_\infty)$ Theorem 7.4(a) provides continuation of $G$ along every such path. For $S$ one must check that the continuation actually exists. For $S$ the starting region is $\operatorname{Re}s>1$ rather than $\operatorname{Re}s>\tfrac12$, and existence along the path is part of the hypothesis; Theorem 7.4(b) explains why it cannot be dropped (continuation of $S$ can fail at points with $\operatorname{Re}s\ge1$, outside the strip where the sheets are built).

### Theorem 1.2: the boundary for admissible germs of $G$ and $S$

The paper proves, under $(\mathrm H_\infty)$: if $g$ is an admissible germ of $G$ at $s_1$, then for every real $y$ and every $r>0$ with $|s_1-(1+iy)|<r$, $g$ does not extend meromorphically to the disc $|s-(1+iy)|<r$; and the same for an admissible germ of $S$ and the disc $|s-iy|<r$.

The condition $|s_1-(1+iy)|<r$ says that the disc centred on the boundary line contains the base point $s_1$ of the germ. For an admissible germ, the theorem rules out a meromorphic function on any such disc that agrees with the branch near its base point. Under $(\mathrm H_\infty)$, Theorem 8.2(a) gives the boundary for every reached germ, including those reached along paths that meet the catalogue or end at catalogue points. The paper adds that the statement for $S$ is not vacuous: under $(\mathrm H_\infty)$ every point of $\{\operatorname{Re}s>0\}\setminus\mathcal C_S$ carries an admissible germ of $S$, so every disc $|s-iy|<r$ contains such base points (proved in Section 8, before the proof of Theorem 1.2). Section 8 also removes the restriction that the path avoid the catalogue and gives a version for connected domains (Theorem 8.2).

### Theorem 1.3: the two further series

The paper says the method is not tied to the kernels of $G$ and $S$, and that Section 9 applies it to $G_2$ and $G_{\log}$, each of which changes one layer of the argument. It sets $\mathcal C_2=\{s:\operatorname{Re}s>\tfrac12,\ 2s\in\Pi\}$, with $\Pi$ as in Section 2 (the set of sums $a+b$ of two points of $\Sigma$). A germ of $G_2$ at $s_1$ is admissible if it is reached from $\operatorname{Re}s>1$ by analytic continuation along a path in $\{\operatorname{Re}s>\tfrac12\}\setminus\mathcal C_2$; a germ of $G_{\log}$ is admissible if it is reached from $\operatorname{Re}s>2$ along a path in $\{\operatorname{Re}s>1\}\setminus\mathcal C_G$.

The paper proves, under $(\mathrm H_\infty)$:

(a) $G_2$ continues analytically along every path in $\{\operatorname{Re}s>\tfrac12\}\setminus\mathcal C_2$ starting in $\operatorname{Re}s>1$, and $G_{\log}$ along every path in $\{\operatorname{Re}s>1\}\setminus\mathcal C_G$ starting in $\operatorname{Re}s>2$. A point carries an admissible germ of $G_2$ if and only if it lies in $\{\operatorname{Re}s>\tfrac12\}\setminus\mathcal C_2$, and one of $G_{\log}$ if and only if it lies in $\{\operatorname{Re}s>1\}\setminus\mathcal C_G$.

(b) If $g$ is an admissible germ of $G_2$ at $s_1$, then for every real $y$ and every $r>0$ with $|s_1-(\tfrac12+iy)|<r$, $g$ does not extend meromorphically to the disc $|s-(\tfrac12+iy)|<r$. The same holds for an admissible germ of $G_{\log}$ and the disc $|s-(1+iy)|<r$.

(c) If $\gamma$ is a path starting in $\operatorname{Re}s>1$ along which $G_2$ continues analytically, with $\gamma(1)\notin\mathcal C_2$, then the terminal germ is admissible. The same holds for $G_{\log}$, with start in $\operatorname{Re}s>2$ and $\gamma(1)\notin\mathcal C_G$.

How the three parts fit. Part (b) is the boundary statement, in the same form as Theorem 1.2. Part (a) plays the role that Theorem 7.4(a) and the paragraph on admissible germs of $S$ play for $G$ and $S$: continuation exists along every allowed path, and admissible germs exist at exactly the points one would expect. The paper draws the consequence right after the theorem: every disc centred on the line contains base points of admissible germs, so (b) is not vacuous, and that $\operatorname{Re}s=\tfrac12$ is a natural boundary of $G_2$ and $\operatorname{Re}s=1$ of $G_{\log}$ once every reached germ is covered. Part (c) is the analogue of Corollary 8.3. It covers arbitrary paths ending off the catalogue. The closing remark covers the remaining endpoints.

Why the same catalogue $\mathcal C_G$ serves $G_{\log}$: its integral has singular points of $P$ on one side and of $Q$ on the other, and both lie in $\Sigma$, so the candidates are again the sums $a+b$ in $\operatorname{Re}s>1$. Why $2s\in\Pi$ for $G_2$: its variable is $v=2s$, and $\operatorname{Re}s>\tfrac12$ is $\operatorname{Re}v>1$.

The remark at the end of the proof of Theorem 1.3(c) covers the remaining endpoints. If continuation exists and ends at a catalogue point, the final holomorphic representative still has a disc on which all nearby germs off the catalogue are admissible. A meromorphic extension of the terminal germ to a boundary-centred disc would agree near the endpoint and hence at some such nearby point inside both discs. That would extend an admissible germ against Theorem 1.3(b). The remark is separate from the numbered theorem. PrimePairNB checks it as `HInf.no_extension_any_path_Sq` and `HInf.no_extension_any_path_mix`, each from `Hinf` and (Z1)–(Z6).

The connected-open-set assertion of Theorem 8.2(b) concerns $G$ and $S$. The full-catalogue assertion in Section 10 concerns $G$ and $T$.

### The novelty paragraph

The paper says it knows of no earlier proof of Theorems 1.1, 1.2 or 1.3 under this hypothesis, nor of a boundary for $G$, $S$, $G_2$ or $G_{\log}$ on every branch; and that under RH the arithmetic is simpler and Section 10 records the extra conclusion that the derivative of the logarithm's coefficient for $G$ and the residue of $T$ are nonzero at every candidate point in $\operatorname{Re}s>1$.

### Corollary 1.4. The unconditional conclusions

The corollary discharges the zero hypotheses of Theorems 1.1, 1.2, 1.3 and 10.1. Each continuation, catalogue and boundary condition in their conclusions still has the scope specified in the theorem. If that proof were withdrawn, Theorems 1.1–1.3 would still stand under $(\mathrm H_\infty)$ and Theorem 10.1 under RH.

Corollary 1.4 is a written deduction. Alpöge's theorem supplies RH for Theorem 10.1. Under RH every non-trivial zero has real part $\tfrac12$, so the exceptional set in $(\mathrm H_\infty)$ is empty for each $\delta>0$. That supplies the zero hypothesis for Theorems 1.1, 1.2 and 1.3. The written proofs use the applicable classical inputs (Z1)–(Z6) and the two zero-free facts following them in Section 2. In Lean, the fact that $\zeta$ has no zeros in $\Re s\ge1$ comes from Mathlib, and the release proves the absence of real zeros in $(0,1)$ from PrimeNumberTheoremAnd's Abel-summation formula.

Section 11 lists three steps taken outside Lean. The author compares the source text defining `RiemannHypothesis` in Mathlib v4.33.1, used by Alpöge with Lean v4.33.1, and Mathlib v4.34.0, used by PrimePairNB with Lean v4.34.0. The text is identical. The comparison leaves agreement of the dependent definitions and equality of the propositions across the builds unchecked in Lean. The written proof supplies the implication from RH to $(\mathrm H_\infty)$, for which the release has no declaration. Finally, the author checks the classical inputs (Z1)–(Z6) against their cited sources by hand. The two Lean developments are built and checked separately.

To see which step is used where, put RH straight into Theorem 10.1. For the first three theorems, fix $\delta>0$ and apply RH to the zeros counted in the definition of $(\mathrm H_\infty)$. Their set is empty, which is stronger than the required finiteness. The classical inputs used in the written argument are unconditional. The paragraph after the corollary makes the same deduction for other statements that assume RH, $(\mathrm H_\infty)$ or $B<1$, leaving their other conditions in force. The proofs of the implications proceed from their stated hypotheses.

## Section 1.4: the idea

The paper splits the proof into two jobs, arithmetic and analysis. At a candidate point $x$, the arithmetic controls a sum over all ordered colliding pairs. For $G$, $S$ and $G_2$ this yields the derivative $X_x'(x)$ of the logarithm's coefficient in $v$. For $T$ it gives the residue and for $G_{\log}$ it gives $-Y_x(x)$. The analysis turns the corresponding nonzero quantity into a continuation obstruction.

### The arithmetic sketch

The paper says $Q=-P'$ is meromorphic on $\operatorname{Re}z>0$ with simple poles in a set $\Sigma$ containing $1$ and the scaled zeros $\rho/k$, $k$ squarefree, because of the Möbius expansion $Q(z)=\sum_k\mu(k)\psi(kz)$ with $\psi=-\zeta'/\zeta$. A Mellin–Barnes integral writes $T$ as an integral of $Q(w)Q(s-w)$ against a Beta kernel, and moving the contour across the poles gives $T$, at a candidate point $x$, at most a simple pole with residue $\sum_{a+b=x}R_aR_b\,\mathrm B(a,b)$, $R_a=\operatorname{Res}_{z=a}Q$, over ordered pairs. The point $x$ is an actual pole of $T$ exactly when this total is not zero; the terms can cancel.

Under RH every point of $\Sigma$ other than $1$ has real part at most $\tfrac12$. So if $x=1+\rho/q$, a pair $(a,b)$ with $a+b=x$ needs $\operatorname{Re}a+\operatorname{Re}b=1+\frac1{2q}>1$, which is impossible unless one of them is $1$. The only pairs are $(1,\rho/q)$ and $(\rho/q,1)$, and the residue is $2R_1R_{\rho/q}\mathrm B(1,\rho/q)$, nonzero exactly when $R_{\rho/q}\ne0$. This residue argument applies for $\operatorname{Re}x>2B_\infty$, where Theorem 4.2 supplies the formula.

Without RH three things can go wrong, the paper says:

1. The residue of $Q$ at $\rho/q$ may be small or zero, because several representations $\rho'/k$ of the same point contribute with signs $\mu(k)$. For prime $q$ and $\operatorname{Re}\rho\ge\tfrac12$ a denominator argument still gives non-vanishing when $q\nmid m(\rho)$, which holds once $q>m(\rho)$ and so for the large $q$ used later; but it does not give the lower bound $1/q$ needed for the comparison. (Section 1.5 credits the denominator step to Titchmarsh's proof.)
2. Finitely many pairs of low height may cancel the main term.
3. The pairs of large height have no uniform cutoff as $x$ approaches the line.

The paper then sketches Section 3. Take $\rho$ on the critical line and $q$ prime. If $\rho/q=\rho'/k$ with another zero $\rho'$, then $\rho'=k\rho/q$, so $\operatorname{Re}\rho'=k/(2q)$. Since $k\ne q$ (otherwise $\rho'=\rho$), $\rho'$ is off the critical line, and its real part is a fraction with denominator $q$ or $2q$. Since $\operatorname{Re}\rho'<1$, $k<2q$, so $\operatorname{Im}\rho'=k\gamma/q<2\gamma$; for $\gamma\le X$ that is a zero of height below $2X$, of which there are at most $N(2X)\approx\frac{X}{\pi}\log X$. The paper's counts: $\gg X^2/\log^2X$ pairs $(\rho,q)$ in a window, $O(X\log X)$ of them spoiled. The low pairs (height at most $H=2\log X$) are $\log^{O(1)}X$ in number, each spoiling one point. The high pairs contribute at most $e^{-H}=X^{-2}$, against a main term of size about $1/X$. The kernel of $S$ decays at half the rate and is estimated separately; the paper notes that any exponential rate would do, with $H$ a suitable multiple of $\log X$, since the near-pair count stays polylogarithmic, and that $H=2\log X$ suits both kernels.

Keep in mind from Section 1.2 that the arithmetic theorem needs only $B<1$; Section 3 says that under that assumption alone a fixed $x$ might have infinitely many pairs, so part of its theorem is that the sums converge absolutely. This is about Section 3 only; Lemma 2.3 itself has no hypothesis, and the paper says everything in Sections 5 to 7 holds without $(\mathrm H_\infty)$, in $\mathcal V_\infty$. $(\mathrm H_\infty)$ enters in Section 8, by making $\mathcal V_\infty=\mathcal V$, so that the unconditional analysis reaches the line.

### The continuation sketch

The paper says that for $G$ and $S$ the integrand $P(z)P(v-z)$ has a left family of singular points $a\in\Sigma$, fixed, and a right family $v-b$, moving with $v$; when $v-b$ meets $a$, at $v=a+b$, the contour is pinched. Instead of continuing along paths, the paper fixes a direction, cuts along parallel rays from every singular point, gets a single-valued branch of $P$ and a sheet $D^\kappa$ defined by one contour integral; near a candidate point,
$$D^\kappa(v)=\operatorname{Log}_\kappa(v-x)\,X_x(v)+H(v),\qquad X_x(v)=\sum_{a+b=x}c(a)c(b)\int_a^{v-b}\mathcal K(z,v)\,dz,$$
with $H$ holomorphic near $x$ and $c(a)=-R_a$. Rotating the direction changes the sheet by integer combinations of $2\pi iX_x$, which are holomorphic on the kernel domain $\mathcal V$, so no local coefficient changes. Along the paths described below, each reached branch is a sheet plus such a combination, with the additional constant allowed for $S$. At the points supplied by Section 3 in the continuation region, the controlled sum gives $X_x'(x)\ne0$. Thus $X_x$ has a nontrivial logarithmic contribution on a punctured neighbourhood, and a meromorphic extension would contradict its monodromy.

Pinching, in a picture: the integral $\int_{(c)}\mathcal K(z,v)P(z)P(v-z)\,dz$ runs up a vertical line between the two families. As $v$ moves, the right family moves with it. As long as the line can be bent to keep the left points on its left and the right points on its right, the integral is a holomorphic function of $v$. When a right point $v-b$ lands on a left point $a$, the path is trapped between them and cannot be bent round; that is where the integral can be singular. The primer's topic "Pinch (Picard–Lefschetz) singularities and the local logarithm" covers this.

$\operatorname{Log}_\kappa$ is a logarithm with its cut along a ray in direction $\kappa$ (defined in Section 5.1). The monodromy argument: going once counterclockwise round $x$, on a small loop that encloses no other candidate point, adds $2\pi i X_x$ to the function. If $X_x$ is not identically zero, the function is not single-valued near $x$, so it cannot equal a meromorphic function there.

There are two path statements. The sheet construction describes a germ reached along a path avoiding the candidate points in its domain. For $S$, Theorem 7.4(b) also permits excursions out of the strip to the right, provided continuation exists and the path ends back in the strip. Under $(\mathrm H_\infty)$ the boundary argument handles arbitrary paths of analytic continuation. Corollary 8.3 for $G,S$ and Theorem 1.3(c) for $G_2,G_{\log}$ give admissibility when the endpoint lies off the catalogue. At a catalogue endpoint, the boundary obstruction instead uses an admissible germ at a nearby point in the same holomorphic representative.

### Two more kernels, and Table 1

The paper closes Section 1.4 with a paragraph on the two series of Theorem 1.3, which show which layer of the argument depends on what.

For $G_2$, in the variable $v=2s$, the integral has the same form with the kernel $\tfrac12\Gamma(z/2)\Gamma((v-z)/2)/\Gamma(v/2)$, holomorphic on the half-plane $\operatorname{Re}v>1$ as the kernel of $G$ is (in full: for $v$ in that half-plane and $0<\operatorname{Re}z<\operatorname{Re}v$, which is (K1)). Sheets, local model, rotation and obstruction carry over unchanged. Only the arithmetic sum changes, to $\sum c(a)c(b)\mathrm B(a/2,b/2)$, and the counting argument is run again for it.

For $G_{\log}$ one factor of the integrand is $Q$, so at a pinch a logarithm meets a pole. The local calculation becomes a residue, the coefficient of the logarithm becomes the value $Y_x(s)=-\sum c(a)c(b)K_s(s-b)$ of the kernel at the pole, and at $s=x$ this is $-\Theta_G(x)$, minus the residue of $T$ at $x$. So the arithmetic for $G_{\log}$ is that of $T$ and $G$, unchanged.

Table 1 (the strategy map) lists, for each series, the variable $v$, what meets at a pinch, the quantity that must be non-zero at $x$, and the sections that prove each step:

| Series | Variable | At a pinch | Must be non-zero at $x$ |
|---|---|---|---|
| $T$ | $v=s$ | pole meets pole | residue $\Theta_G(x)$ |
| $G_{\log}$ | $v=s$ | logarithm meets pole | $Y_x(x)=-\Theta_G(x)$ |
| $G$ | $v=s$ | two logarithms | $X_x'(x)=\Theta_G(x)$ |
| $G_2$ | $v=2s$ | two logarithms, new kernel | $X_x'(x)=\tfrac12\Theta_2(x)$ |
| $S$ | $v=2s+1$ | two logarithms, kernel on a strip | $X_x'(x)=\tfrac12\Theta_S(x)$ |

Derivatives are in $v$. Read the table down its third column: from $T$ to $G$ each row replaces a pole by a logarithm, and the quantity that carries the obstruction moves from a residue, to a value of the coefficient, to a derivative of the coefficient. The last two rows keep two logarithms and change the kernel. The table's last column in the paper says where each step is proved; the parts of Section 9 named there replace only the step that changes.

## Section 1.5: credit

The paper's credits, in the order it gives them:

- The natural boundary of $P$ is due to Landau and Walfisz; the paper points to Titchmarsh (§9.5), who credits them, and to Dahlquist. Kluyver had asserted it under RH, without details; Landau reconstructed his argument and proved the assertion under RH. Dahlquist likewise credits Kluyver, under RH, with the natural boundary of $e^P$. The denominator step in the non-vanishing of $R_{\rho/p}$ is Titchmarsh's proof of his (9.5.7).
- For Euler products $\prod_ph(p^{-s})$, where $h$ is analytic with $h(0)=1$ and has no limit point of zeros or singularities in $|z|\le1$, Dahlquist proved that the imaginary axis is a natural boundary except when the product is a finite product of powers $\zeta(\nu s)^{\beta_\nu}$. Estermann had treated the case in which $h$ is a polynomial with integral coefficients (the paper cites this through Dahlquist); Titchmarsh cites him for the natural boundary $\operatorname{Re}s=0$ of $\sum_nd_k(n)^ln^{-s}$, $k\ge2$, except when $l=1$ or $l=k=2$.
- Egami and Matsumoto isolate a main pair of zeros and bound the rest by the decay of the Gamma factors, under their condition (B). The comparison of a main term with far pairs is in Bhowmik and Schlage-Puchta. Both remove near pairs by a hypothesis on additive relations among ordinates. In Bhowmik and Schlage-Puchta's form, their Conjecture 1, it says that $\gamma_1+\gamma_2=\gamma_3+\gamma_4\ne0$ forces $\{\gamma_1,\gamma_2\}=\{\gamma_3,\gamma_4\}$; Fujii noted that the conjectured linear independence of the positive ordinates implies that a sum $\gamma+\gamma'$ has essentially one representation. In the paper's setting the abundance of the points $\rho/q$ lets the near-pair count of Section 3 take the place of that hypothesis; the paper adds that this "says nothing about the hypothesis in their setting".
- That zeros scaled by $1/p$, for $p$ prime in a window, are too many for the zeros of $\zeta$ to cancel them all is Bhowmik and Schlage-Puchta's earlier idea, for Euler products of shifted zeta factors, where cancellation is an exact coincidence of a zero with a pole. Theorem 3.3 is that count in this setting, and it must also supply the lower bound $|c(u)|\ge1/q$.
- Separating contours for the multiplicative kernel $dz/z$ go back to Hadamard and Borel; cut domains, for finitely many singular points, are Hadamard's. For the local jump of a pinched integral the paper cites Pham's formula (Disc 1), and for his mixed case, a polar locus meeting a ramified one, (Disc 4). For Hadamard products it cites Pérez-Marco. The paper adapts these to an additive kernel integral over an infinite contour.
- That a convolution can develop singularities at sums of singular points, with a monodromy that depends on the path, is standard in resurgence theory, for integrals from $0$ over a discrete set of singular points (Sauzin; Ou and Delabaere). The paper uses no theorem from there, since its contour is infinite and the singular points accumulate at the line.
- Two theorems on Dirichlet series attached to polynomials do not apply. Tanigawa and Zhai's condition C1 asks for auxiliary series meromorphic on all of $\mathbb C$, which $P$ and $Q$ are not. Peter's theorem, on a polynomial evaluated at sequences with weights taken from auxiliary Dirichlet series, asks each auxiliary series to be meromorphic on $\mathbb C$ with finitely many poles in each vertical strip of finite width; here the auxiliary series are $P$ and $Q$, for which $\operatorname{Re}z=0$ is a natural boundary.
- Matsumoto's survey describes recent results on multiple Dirichlet series with arithmetic coefficients in the numerators, among them those for series weighted by $\Lambda$. For a function-field analogue of the $\Lambda$-weighted Goldbach series, Egami and Matsumoto prove unconditionally that it continues meromorphically to $\mathbb C$ when the two function fields have the same characteristic, and has the natural boundary $\operatorname{Re}s=2$ when they do not.
- The results for series weighted by $\Lambda$ do not transfer when the sums over prime powers are replaced by sums over primes, since the poles of $-\zeta'/\zeta$ in $\operatorname{Re}z>0$ are confined to $1$ and the unscaled zeros. The Möbius expansion of $Q$ introduces additional scaled-zero candidates, and the non-cancellation argument supplies actual poles among them. The contour shift of those results does carry over to $T$; Section 4 opens with that credit.
- For $G_2$ and $G_{\log}$ the Mellin–Barnes integrals come from the same formula of Egami and Matsumoto: for $G_2$ with $p^2,q^2$ in place of $p,q$, and for $G_{\log}$ with the weight $\log q$ on one prime. For the weighted analogue $\sum\Lambda(m)\Lambda(n)(m^2+n^2)^{-s}$ of $G_2$, Tanigawa and Zhai use the same formula, with $-\zeta'/\zeta$ at a doubled argument in each factor (the paper writes "$-\zeta'/\zeta(2z)$ in each factor"; with Mellin variable $z$ the two arguments are the complementary ones, $2z$ and $2(s-z)$), and state that under RH it continues meromorphically only to $\operatorname{Re}s>\tfrac12$; Egami and Matsumoto write that the proof of the natural-boundary claim of Tanigawa and Zhai's Theorem 1.3 "seems incomplete". El-Gammal studies $G_2$ and conjectures that it continues meromorphically to at least $\operatorname{Re}s>0$; under $(\mathrm H_\infty)$, Theorem 1.3(b) shows that it does not.

The paper reports Tanigawa and Zhai's assertion for the weighted analogue and Egami and Matsumoto's assessment of their proof. El-Gammal's conjecture concerns $G_2$ itself.

Section 1.5 refutes El-Gammal's Conjecture 7.8 without any hypothesis on the zeros. The prime number theorem gives a count of order $X/\log^2 X$ for the ordered pairs with $p^2+q^2\le X$. Partial summation gives convergence at $s=1$ and divergence at every real $s<1$. The coefficients are nonnegative, so Landau's theorem makes $s=1$ singular. The finite limit $G_2(1)$ along the real axis from the right excludes a pole. This rules out a single meromorphic continuation to $\Re s>0$. The point $s=1$ belongs to $\mathcal C_2$ because $2=1+1\in\Pi$. Paths can cross $\Re s=1$ at points off the catalogue as in Theorem 1.3(a), and the every-branch boundary is $\Re s=\tfrac12$. The argument at $s=1$ is outside the Lean release.

## Section 1.6: organization

The paper gives the section plan: inputs (Section 2), non-cancellation (Section 3), $T$ (Section 4), sheets, local model and branches (Sections 5 to 7), boundary (Section 8), $G_2$ and $G_{\log}$ with the proof of Theorem 1.3 (Section 9), RH (Section 10), Lean (Section 11).

## Check your understanding

1. Why does Theorem 1.1's "infinitely many poles in every disc" imply that no meromorphic function on a disc agrees with $T$?
2. Under RH, why does $x=1+\rho/q$ have only two pairs?
3. What would go wrong with the argument if two pairs at the same point contributed $+1$ and $-1$?

Answers. (1) Meromorphic functions have finitely many poles in a compact set. (2) Every other point of $\Sigma$ has real part at most $\tfrac12$, so a pair not using $1$ has real parts summing to at most $1<\operatorname{Re}x$. (3) The sum $X_x'(x)$ would be zero, so the leading $\delta\log\delta$ term would vanish and the argument would give no obstruction at that point. The point is regular only if $X_x\equiv0$.

# 2. Section 2: the prime zeta function and two kernels

## The section opener

The paper says this section fixes the classical inputs, the function $Q$ and the set $\Sigma$, the two kernels, and the coefficient $X_x$; and that without RH $\Sigma$ is only a set of candidates, since a point with several representations may have coefficient zero.

## Section 2.1: notation and classical inputs (Z1) to (Z6)

### Table 2, notation

The section opens with a notation table. For each principal symbol of the paper ($\mathcal Z$ and $m(\rho)$, $B$ and $B_\infty$, $\Sigma$, $c(a)$ and $R_a$, $\Pi$ and $\mathcal X$, $F_\delta$, $\mathcal K$, $\mathcal V$, $\mathcal V_\infty$, $D$, $K$, $K_s$, the three catalogues, $J_{ab}$, $X_x$, $M_x$, $\Theta_G$, $\Theta_S$, $D^\kappa$ and $\mathcal M$, $e$, $\operatorname{Log}_\kappa$, $P^\kappa$, the cuts and cut domains, $\Theta_2$, $Y_x$, $D^\kappa_{\log}$ and $\mathcal M_{\log}$) it gives the meaning and the place of definition. Use it with the symbol table at the end of this guide.

The paper fixes: $p,q$ primes; $\rho=\beta+i\gamma$ ranging over $\mathcal Z$; $m(\rho)$ the multiplicity; $\mathrm B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$, the Beta function; $N(t)=\sum_{0<\gamma\le t}m(\rho)$, the zero count with multiplicity; $N_0(t)$, the number of distinct zeros on the critical line with $0<\gamma\le t$. Then six cited facts:

- (Z1) Symmetry: with $\rho$, also $\bar\rho$ and $1-\bar\rho$ are zeros, with the same multiplicity (conjugation and the functional equation).
- (Z2) Riemann–von Mangoldt: $N(t)=\frac t{2\pi}\log\frac t{2\pi}-\frac t{2\pi}+O(\log t)$, and $N(t+1)-N(t)\le C_1\log(t+3)$ for $t\ge0$.
- (Z3) The local expansion of $\zeta'/\zeta$: for $-1\le\operatorname{Re}z\le2$, $|\operatorname{Im}z|\ge2$, $\zeta(z)\ne0$, $\zeta'/\zeta(z)$ differs from the sum of $m(\rho)/(z-\rho)$ over zeros within height $1$ by at most $C\log|\operatorname{Im}z|$.
- (Z4) Hardy–Littlewood: $N_0(t)\ge A_0t$ for $t\ge t_0$, counting distinct zeros.
- (Z5) Primes in intervals: for fixed $\theta>0$ and large $x$, $(x,(1+\theta)x)$ holds at least $\theta x/(2\log x)$ primes.
- (Z6) Stirling's bound: for $x$ in a compact interval $[x_1,x_2]\subset(0,\infty)$, $|\Gamma(x+iy)|\le C(1+|y|)^{x_2}e^{-\pi|y|/2}$.

Plus two more: $\zeta(s)\ne0$ for $\operatorname{Re}s\ge1$, and $\zeta$ has no real zero in $(0,1)$. The paper says the Lean proofs take these two from libraries, not as hypotheses. None of the eight assumes RH or $(\mathrm H_\infty)$. For (Z3) the paper notes that Titchmarsh states it for large positive height, and that bounded heights are handled by subtracting the local poles and negative heights by conjugation. The paper defines
$$B=\sup_\rho\operatorname{Re}\rho,\qquad B_\infty=\lim_{t\to\infty}\sup_{|\gamma|\ge t}\operatorname{Re}\rho,$$
notes $(\mathrm H_\infty)$ says $B_\infty=\tfrac12$, and that $\tfrac12\le B_\infty\le B\le1$, and $B<1$ under $(\mathrm H_\infty)$.

What each input is for:

- (Z1) gives the reality and symmetry of $c(a)$ in Lemma 2.1, and the lower bound $B_\infty\ge\tfrac12$: if $\rho=\beta+i\gamma$ is a zero, so is $1-\bar\rho=(1-\beta)+i\gamma$, at the same height, and one of $\beta$, $1-\beta$ is at least $\tfrac12$. So at every height where there is a zero there is one with real part $\ge\tfrac12$, and there are zeros at arbitrarily large heights.
- (Z2) is used twice: the second clause bounds multiplicities ($m(\rho)\le N(\gamma)-N(\gamma-1)$ for $\gamma>0$, after conjugating a zero of negative height to positive height by (Z1); at most $C_1\log(|\gamma|+3)$ up to a factor), and bounds how many zeros sit in a unit window; the first clause gives $N(2X)\ll X\log X$ in Section 3.
- (Z3) is the tool for bounding $\psi=-\zeta'/\zeta$ away from zeros (Lemma 2.2). It says $\zeta'/\zeta$ is a logarithm in size, apart from the poles of nearby zeros.
- (Z4) supplies many zeros on the line to build points $1+\rho/q$. The paper insists the count is of distinct zeros, and its bound in Theorem 3.3(a) is stated with that count; a zero of multiplicity $m$ counted $m$ times would not produce $m$ different points.
- (Z5) supplies many primes $q$ in a window.
- (Z6) is the exponential decay behind the Beta kernels. It bounds the kernels of $G$ and $T$ (and, in Section 9, of $G_2$ and $G_{\log}$), which makes their contour integrals converge and kills their high pairs. For the kernel of $G$, two Gamma factors in the numerator give decay $e^{-\pi|\operatorname{Im}z|}$ in total. The kernel of $S$ needs no Stirling input: its bound comes directly from $K(w)=(1-w)\pi/\sin\pi w$ and a lower bound for the sine, in (K2) and again in Lemma 3.4, and Section 11 records that the formal theorem for $S$ does not use (Z6).

On (Z4): the paper notes the printed theorems do not say "distinct", but their proofs find zeros (sign changes of a real function on the line) in disjoint intervals, so they are distinct, and a zero at a shared endpoint costs a factor $2$. This is a reading of the cited proofs, not a new result.

What $B_\infty$ measures: $\sup_{|\gamma|\ge t}\operatorname{Re}\rho$ is the supremum of the real parts of the zeros of height at least $t$; like $B$, it is a supremum and need not be attained by any zero. As $t$ increases, the set shrinks, so the supremum does not increase, and the limit exists. Under $(\mathrm H_\infty)$ the supremum at a finite cutoff can still exceed $\tfrac12$; only its limit is $\tfrac12$. $B_\infty$ ignores any finite set of zeros. $(\mathrm H_\infty)$ is the statement that this limit is $\tfrac12$: for each $\delta$, from some height on, every zero has real part at most $\tfrac12+\delta$, so only the finitely many zeros below that height can exceed it.

## Equation (2): $\Sigma$, $\operatorname{ord}$, $c(a)$ and $R_a$

The paper defines $P(z)=\sum_p p^{-z}$, $Q(z)=-P'(z)=\sum_p\log p\,p^{-z}$ for $\operatorname{Re}z>1$, $\psi=-\zeta'/\zeta$,
$$\Sigma=\{1/k:k\ge1\text{ squarefree}\}\cup\{\rho/k:\rho\in\mathcal Z,\ k\ge1\text{ squarefree}\},$$
$\operatorname{ord}_w\zeta$ equal to $m(w)$ at a zero, $-1$ at $w=1$, and $0$ elsewhere in $\operatorname{Re}w>0$, and for $\operatorname{Re}a>0$
$$c(a)=\sum_{k\ge1}\frac{\mu(k)}k\operatorname{ord}_{ka}\zeta,\qquad R_a=-c(a).\tag{2}$$
The sum is finite since $ka$ is a zero or $1$ only if $k\operatorname{Re}a\le1$.

New symbols. $\mu(k)$ is the Möbius function: $0$ if $k$ has a squared prime factor, $(-1)^j$ if $k$ is a product of $j$ distinct primes. So only squarefree $k$ contribute. "Squarefree" means no prime divides $k$ twice. $\operatorname{ord}_w\zeta$ is the order of $\zeta$ at $w$: positive at a zero, $-1$ at the pole $w=1$.

A worked case. Take $a=1$. The terms are $k=1$: $\mu(1)\operatorname{ord}_1\zeta=-1$; $k\ge2$: $ka=k$ is real and at least $2$, not a zero and not $1$, so $0$. Hence $c(1)=-1$, $R_1=1$. Take $a=1/k_0$ with $k_0$ squarefree: the only term is $k=k_0$, giving $c(1/k_0)=-\mu(k_0)/k_0\ne0$ (there are no real zeros in $(0,1)$, so $j/k_0$ is never a zero). Take $a=\rho/q$ with $\rho$ a simple zero and $q$ prime, and suppose no other representation. The only term is $k=q$: $c(\rho/q)=\mu(q)/q=-1/q$. That is the size $1/q$ Section 3 relies on.

How $c(a)$ can vanish: if $a=\rho/q=\rho'/k$ with two different zeros, both $k=q$ and the other $k$ contribute, with signs $\mu(q)=-1$ and $\mu(k)$, and the sum can be zero.

## Lemma 2.1: $Q$, its poles, and $\Sigma$

The paper proves: (i) $Q$ continues meromorphically to $\operatorname{Re}z>0$, with $Q(\bar z)=\overline{Q(z)}$; its poles are simple and lie in $\Sigma$; $\operatorname{Res}_{z=a}Q=R_a$, so $a$ is a pole if and only if $c(a)\ne0$; $c(1)=-1$; $c(a)$ is real and $c(\bar a)=c(a)$. (ii) $\Sigma$ is locally finite in $\operatorname{Re}z>0$; every point other than $1$ has real part at most $B$; every point that is neither $1$ nor a zero has real part at most $\tfrac12$; for $\delta>0$, $F_\delta=\{a\in\Sigma:\operatorname{Re}a>B_\infty+\delta\}$ is finite and lies in $\{1\}\cup\mathcal Z$. (iii) For $\varepsilon\in(0,1)$, $|c(a)|\le C(\varepsilon)\log(|\operatorname{Im}a|+3)$ for $a\in\Sigma$ with $\operatorname{Re}a\ge\varepsilon$, and at most $C(\varepsilon)\log(|t|+3)$ such points have $t\le\operatorname{Im}a\le t+1$.

### Part (i), the steps

The identity $\psi(z)=\sum_{j\ge1}Q(jz)$. For $\operatorname{Re}z>1$, $\psi(z)=\sum_n\Lambda(n)n^{-z}$, where $\Lambda(p^j)=\log p$ and $\Lambda=0$ off prime powers (see the primer, "$Q=-P'$, the candidate set $\Sigma$, and the coefficient $c(a)$", and the $\Phi_2$ primer for the von Mangoldt function). Group by $j$:
$$\psi(z)=\sum_p\sum_{j\ge1}\log p\,p^{-jz}=\sum_{j\ge1}\sum_p\log p\,p^{-jz}=\sum_{j\ge1}Q(jz).$$

Möbius inversion. Substitute this into $\sum_k\mu(k)\psi(kz)$:
$$\sum_k\mu(k)\psi(kz)=\sum_k\mu(k)\sum_jQ(jkz)=\sum_{m\ge1}Q(mz)\sum_{k\mid m}\mu(k)=Q(z),$$
since $\sum_{k\mid m}\mu(k)$ is $1$ for $m=1$ and $0$ otherwise. Regrouping a double sum by $m=jk$ needs absolute convergence: the number of ways to write $m=jk$ is the divisor count $d(m)$, and $|Q(mz)|\le Q(m\operatorname{Re}z)$, so the paper's condition $\sum_m d(m)Q(m\operatorname{Re}z)<\infty$ is what is needed. It holds because $Q(m\sigma)\le\sum_n\log n\,n^{-m\sigma}\ll2^{-m\sigma}$ for large $m$, which beats $d(m)\le m$.

The tail bound. The paper uses that $\psi(x)2^x$ is non-increasing for real $x>1$. Indeed $\psi(x)2^x=\sum_n\Lambda(n)(2/n)^x$, and each $(2/n)^x$ with $n\ge2$ is non-increasing in $x$. So for $kx_0\ge2$,
$$|\psi(kz)|\le\psi(k\operatorname{Re}z)\le\psi(kx_0)\le\psi(2)\,2^{2}\,2^{-kx_0}.$$
These bounds form a convergent geometric series in $k$, so $\sum_{k\ge2/x_0}\mu(k)\psi(kz)$ converges uniformly on $\operatorname{Re}z\ge x_0$ to a holomorphic function; the finitely many terms with $k<2/x_0$ are meromorphic. Since $x_0>0$ is arbitrary, $Q$ is meromorphic on $\operatorname{Re}z>0$.

The residues. $\psi=-\zeta'/\zeta$ has a simple pole at each zero $w_0$ of order $m$ with residue $-m$, and at $w=1$ with residue $+1$; in both cases the residue is $-\operatorname{ord}_{w_0}\zeta$ (see the primer, "$Q=-P'$, the candidate set $\Sigma$, and the coefficient $c(a)$"). For $\psi(kz)$ near $z=a$ with $ka=w_0$:
$$\psi(kz)\approx\frac{-\operatorname{ord}_{w_0}\zeta}{kz-ka}=\frac{-\operatorname{ord}_{ka}\zeta/k}{z-a}.$$
Multiply by $\mu(k)$ and sum over $k$: $\operatorname{Res}_aQ=-\sum_k\frac{\mu(k)}k\operatorname{ord}_{ka}\zeta=-c(a)=R_a$. Every pole of a term is at a point $a$ with $ka\in\{1\}\cup\mathcal Z$, that is, $a\in\Sigma$. Poles of different terms can sit at the same $a$ and add; the sum is still at most a simple pole, and is a pole exactly when $c(a)\ne0$.

Reality. $\mu(k)/k$ and $\operatorname{ord}$ are real, so $c(a)$ is real. By (Z1) $\bar\rho$ is a zero of the same multiplicity, so $\operatorname{ord}_{k\bar a}\zeta=\operatorname{ord}_{ka}\zeta$ and $c(\bar a)=c(a)$. $Q$ has real coefficients, so $Q(\bar z)=\overline{Q(z)}$.

### Part (ii), the steps

Local finiteness: on $\operatorname{Re}z\ge x_0$ a point $\rho/k$ or $1/k$ needs $k\le1/x_0$, and in a bounded region each such $k$ gives finitely many zeros (zeros of a non-zero holomorphic function are isolated, and (Z2) counts them).

Real parts: $1/k\le\tfrac12$ for $k\ge2$; $\operatorname{Re}(\rho/k)=\operatorname{Re}\rho/k<1/k\le\tfrac12$ for $k\ge2$; and for $k=1$ the point is a zero, with real part at most $B$. So a point that is neither $1$ nor a zero has real part at most $\tfrac12$.

$F_\delta$: since $B_\infty\ge\tfrac12$, a point with real part above $B_\infty+\delta>\tfrac12$ is $1$ or a zero; by the definition of $B_\infty$ only finitely many zeros have real part above $B_\infty+\delta$.

### Part (iii), the steps

Only $k\le1/\varepsilon$ contribute to $c(a)$ when $\operatorname{Re}a\ge\varepsilon$. Each term with $ka$ a zero is at most $m(ka)$ in modulus, the term with $ka=1$ (order $-1$, not a multiplicity) is bounded separately by $1$, and a zero at height $h$ has multiplicity at most the number of zeros in a unit window around $h$, which (Z2) and (Z1) bound by $2C_1\log(|h|+3)$. With $|h|=k|\operatorname{Im}a|\le|\operatorname{Im}a|/\varepsilon$, $\log(|h|+3)\le\log(1/\varepsilon)+\log(|\operatorname{Im}a|+3)$, absorbed into $C(\varepsilon)$. For the count: a point $\rho/k$ with $t\le\operatorname{Im}\le t+1$ needs $\rho$ at height in $[kt,kt+k]$, which is $k$ unit windows of $O(\log(k|t|+3))$ zeros each, and $k\le1/\varepsilon$.

What Lemma 2.1 is for: it locates every possible singularity of $Q$ (and of $P$) and gives the size bounds used in Section 3 to estimate sums over high pairs.

## Lemma 2.2: logarithmic growth of $Q$

The paper proves: let $\delta>0$ and $t_\delta\ge2$ be such that every zero with $|\gamma|\ge t_\delta-1$ has $\operatorname{Re}\rho\le B_\infty+\delta$; then $|Q(w)|\le C_\delta\log|\operatorname{Im}w|$ for $\operatorname{Re}w\ge B_\infty+2\delta$, $|\operatorname{Im}w|\ge t_\delta$.

Such a $t_\delta$ exists by the definition of $B_\infty$. The steps:

1. Write $Q(w)=\psi(w)+\sum_{k\ge2}\mu(k)\psi(kw)$.
2. For $k\ge2$, $\operatorname{Re}(kw)\ge2(\tfrac12+2\delta)=1+4\delta$, using $B_\infty\ge\tfrac12$. So $|\psi(kw)|\le\psi(k(\tfrac12+2\delta))$, and the tail bound from Lemma 2.1 makes the sum over $k$ converge to a constant depending on $\delta$.
3. If $\operatorname{Re}w\ge2$, $|\psi(w)|\le\psi(2)$.
4. Otherwise $B_\infty+2\delta\le\operatorname{Re}w<2$ and $|\operatorname{Im}w|\ge t_\delta\ge2$, so (Z3) applies (and $\zeta(w)\ne0$, since no zero lies that far right at that height). Each zero in its local sum has $|\gamma-\operatorname{Im}w|\le1$, hence $|\gamma|\ge t_\delta-1$, hence $\operatorname{Re}\rho\le B_\infty+\delta$, hence $|w-\rho|\ge\operatorname{Re}w-\operatorname{Re}\rho\ge\delta$. Each term is at most $m(\rho)/\delta$, and the multiplicities in a window of width $2$ add up to $O(\log|\operatorname{Im}w|)$ by (Z2).

What it is for: every contour in the paper runs to infinite height, and the integrand must be integrable there. The kernel decays exponentially and $Q$ (or $P$) grows at most like a logarithm, so the product is integrable. The paper's sentence before the lemma explains the shape: without RH the bound can only hold right of $B_\infty$, and only above the finitely many zeros further east.

## Section 2.3: the kernels, (K1) to (K3), equations (3) and (4)

The paper introduces the pinching variable $v$: $v=s$ for $G$ and $T$, $v=2s+1$ for $S$; the domains and kernels
$$G:\ \mathcal V=\{\operatorname{Re}v>1\},\ \mathcal K(z,v)=\frac{\Gamma(z)\Gamma(v-z)}{\Gamma(v)};\qquad S:\ \mathcal V=\{1<\operatorname{Re}v<3\},\ \mathcal K(z,v)=\tfrac12K\Bigl(\frac{2z-v+3}4\Bigr),\ K(w)=\Gamma(w)\Gamma(2-w);$$
$D(v)=G(v)$ or $D(v)=S((v-1)/2)$; and $\mathcal V_\infty=\mathcal V\cap\{\operatorname{Re}v>2B_\infty\}$, which is $\mathcal V$ under $(\mathrm H_\infty)$. Three facts:

- (K1) $\mathcal K$ is holomorphic for $v\in\mathcal V$, $0<\operatorname{Re}z<\operatorname{Re}v$.
- (K2) Locally uniformly, $\mathcal K(z,v)\ll(1+|\operatorname{Im}z|)^Ae^{-\pi|\operatorname{Im}z|/2}$.
- (K3) For $\operatorname{Re}v>2$ (and $<3$ for $S$) and $1<c<\operatorname{Re}v-1$, equation (3): $D(v)=\frac1{2\pi i}\int_{(c)}\mathcal K(z,v)P(z)P(v-z)\,dz$.

And for $T$, equation (4): $T(s)=\frac1{2\pi i}\int_{(c)}K_s(w)Q(w)Q(s-w)\,dw$ with $K_s(w)=\Gamma(w)\Gamma(s-w)/\Gamma(s)$, the kernel of $G$.

Notation. $\int_{(c)}$ is the integral up the vertical line $\operatorname{Re}z=c$, from $c-i\infty$ to $c+i\infty$.

### Why $\mathcal K$ is holomorphic (K1)

For $G$: $\Gamma$ has poles only at $0,-1,-2,\dots$, so $\Gamma(z)$ is holomorphic for $\operatorname{Re}z>0$ and $\Gamma(v-z)$ for $\operatorname{Re}z<\operatorname{Re}v$; $1/\Gamma$ is entire. For $S$: the reflection formula $\Gamma(w)\Gamma(1-w)=\pi/\sin\pi w$ and $\Gamma(2-w)=(1-w)\Gamma(1-w)$ give $K(w)=(1-w)\pi/\sin\pi w$, holomorphic except at integers $w\le0$ and $w\ge2$ (at $w=1$ the zero of $1-w$ cancels the zero of $\sin\pi w$). With $w=(2z-v+3)/4$ and $0<\operatorname{Re}z<\operatorname{Re}v$,
$$\frac{3-\operatorname{Re}v}4<\operatorname{Re}w<\frac{\operatorname{Re}v+3}4,$$
and $1<\operatorname{Re}v<3$ makes this interval sit inside $(0,\tfrac32)$. That is the only use of the upper bound $\operatorname{Re}v<3$.

### Why the kernels decay (K2)

For $G$, (Z6) applied to both numerator factors gives $e^{-\pi|\operatorname{Im}z|/2}e^{-\pi|\operatorname{Im}(v-z)|/2}$, which for $v$ in a compact set is $\ll e^{-\pi|\operatorname{Im}z|}$; $1/|\Gamma(v)|$ is bounded on compacts. For $S$, $|\sin\pi w|\ge\tfrac12(e^{\pi|\operatorname{Im}w|}-1)$ and $\operatorname{Im}w=\operatorname{Im}(2z-v)/4$, about $\tfrac12\operatorname{Im}z$, so $|K(w)|\ll(1+|\operatorname{Im}z|)e^{-\pi|\operatorname{Im}z|/2}$. That is the "half the rate".

### Equation (3), the Mellin–Barnes integral for $G$ and $S$

#### Deriving the integral for $G$

The Mellin–Barnes integral (see the primer, "The Mellin–Barnes representation"): for $x>0$ and $0<d<\operatorname{Re}s$,
$$(1+x)^{-s}=\frac1{2\pi i}\int_{(d)}\frac{\Gamma(w)\Gamma(s-w)}{\Gamma(s)}x^{-w}\,dw.$$
Write $(p+q)^{-s}=q^{-s}(1+p/q)^{-s}$ and put $x=p/q$: the integrand becomes $\mathcal K(z,s)\,p^{-z}q^{z-s}=\mathcal K(z,s)p^{-z}q^{-(s-z)}$. Summing over $p,q$ gives $P(z)P(s-z)$ inside, provided the sum and integral can be swapped.

#### Deriving the integral for $S$

The paper's steps, checked:

1. $p^{1-s}q^{2-s}(p^2+q^2)^{-2}=p^{1-s}q^{2-s}q^{-4}(1+(p/q)^2)^{-2}=p^{1-s}q^{-s-2}(1+x)^{-2}$ with $x=(p/q)^2$.
2. The case $s=2$ of Mellin–Barnes: $\Gamma(w)\Gamma(2-w)/\Gamma(2)=K(w)$, so $(1+x)^{-2}=\frac1{2\pi i}\int_{(d)}K(w)x^{-w}dw$ for $0<d<2$.
3. $x^{-w}=p^{-2w}q^{2w}$, so the summand is $\frac1{2\pi i}\int K(w)p^{1-s-2w}q^{-s-2+2w}dw$.
4. Substitute $z=2w+s-1$, so $w=(z-s+1)/2$ and $dw=\tfrac12dz$. The $p$ exponent is $1-s-2w=-z$. The $q$ exponent is $-s-2+2w=-s-2+z-s+1=z-2s-1=-(v-z)$ with $v=2s+1$.
5. In terms of $v$: $w=(z-s+1)/2=(2z-(v-1)+2)/4=(2z-v+3)/4$.

So the integrand is $\tfrac12K((2z-v+3)/4)p^{-z}q^{-(v-z)}$, which is $\mathcal K(z,v)p^{-z}q^{-(v-z)}$, and summing gives (3) for $D(v)=S((v-1)/2)$.

### Fubini

On $\operatorname{Re}z=c$, $|p^{-z}q^{-(v-z)}|=p^{-c}q^{-(\operatorname{Re}v-c)}$, and $\sum_{p,q}p^{-c}q^{-(\operatorname{Re}v-c)}=P(c)P(\operatorname{Re}v-c)$, finite because both exponents exceed $1$, which is why $1<c<\operatorname{Re}v-1$. Times the integrable kernel bound (K2), this is an integrable majorant of the double sum-integral, so Fubini–Tonelli lets the sum move inside. The same with $Q(c)Q(\sigma-c)$ gives (4).

### Equation (4), the integral for $T$

Here $\operatorname{Re}s>2$ and $1<c<\operatorname{Re}s-1$. Multiplying by $\log p\log q$ before summing replaces $P(w)P(s-w)$ by $Q(w)Q(s-w)$. The kernel is unchanged. This matters in Section 4 because $Q$ is single-valued, so shifting the contour across right poles contributes residues.

### Why $S$ lives on a strip

The paper states (3) for $S$ on $2<\operatorname{Re}v<3$, that is $\tfrac12<\operatorname{Re}s<1$, and builds the sheets of $S$ on the strip $\mathcal V=\{1<\operatorname{Re}v<3\}$. The upper limit comes from (K1): only for $\operatorname{Re}v<3$ is the kernel holomorphic on the whole range $0<\operatorname{Re}z<\operatorname{Re}v$, which is the range the separating graphs of Section 5 are allowed to use. The series $S$ itself converges for all $\operatorname{Re}s>\tfrac12$. What stops at $\operatorname{Re}v=3$ is the sheet construction, and the guide does not read the paper as saying that a Mellin–Barnes integral for $S$ fails beyond it.

The constant $C$ of Section 7 comes from here. A path for $S$ may leave the strip on the right, into $\operatorname{Re}v\ge3$, and come back. A germ leaves as $D+m+C$, and on the excursion the correction $m$ has to be continued outside the strip. Its derivative is meromorphic on the whole plane, with possible poles beyond the strip (for a term $J_{ab}$, at $s=a+1$ and $s=b+2$). If the path can be continued at all, the correction returns with the same derivative, so it can differ from $m$ only by a constant (Theorem 7.4(b)).

## Section 2.4: pairs, Lemma 2.3, and the coefficient

Section 2.4 identifies the candidate singularities of the two factors in the integral (3). In their right half-planes these are the points $a\in\Sigma$ for the first factor and $v-b$, $b\in\Sigma$, for the second. A candidate with $c(a)=0$ is regular in the first factor, and likewise a candidate $v-b$ with $c(b)=0$ in the second. For the continuations in Theorem 7.4, singularities in $\mathcal V_\infty$ can occur only where two candidates meet, at $v=a+b$. It defines $\Pi=\Sigma+\Sigma$, $\mathcal X=\Pi\cap\{\operatorname{Re}v>2B_\infty\}$, the catalogues $\mathcal C_G=\Pi\cap\{\operatorname{Re}s>1\}$ and $\mathcal C_S=\{s:\operatorname{Re}s>0,\ 2s+1\in\Pi\}$, and the pairs at $x$: ordered pairs $(a,b)\in\Sigma^2$ with $a+b=x$, a diagonal pair $(a,a)$ counted once.

Note how $\mathcal C_S$ translates: $\operatorname{Re}s>0$ is $\operatorname{Re}v>1$, and the singular points in $v$ are sums $a+b$; so a point $s$ is a candidate when $v=2s+1$ is.

### Lemma 2.3: finitely many pairs

The paper proves that $\mathcal X$ is locally finite in $\operatorname{Re}v>2B_\infty$ and each $x\in\mathcal X$ has finitely many pairs.

The steps. Suppose $\operatorname{Re}x\ge2B_\infty+2\eta$ and $x=a+b$. If both had real part below $B_\infty+\eta$, their sum would be below $2B_\infty+2\eta$; so one, say $a$, has $\operatorname{Re}a\ge B_\infty+\eta>B_\infty+\eta/2$, and lies in the finite set $F_{\eta/2}$ of Lemma 2.1(ii). Then $\operatorname{Re}b=\operatorname{Re}x-\operatorname{Re}a\ge\operatorname{Re}x-1\ge2B_\infty+2\eta-1\ge2\eta$, using $\operatorname{Re}a\le1$ and $B_\infty\ge\tfrac12$. With $x$ in a bounded set, $b=x-a$ lies in a bounded set with real part at least $2\eta$, where $\Sigma$ is finite by local finiteness. So finitely many pairs, and finitely many sums in any bounded part of $\operatorname{Re}v\ge2B_\infty+2\eta$.

What it is for: the lemma has no hypothesis. It makes the local model of Section 6 a finite sum and the catalogue discrete in $\operatorname{Re}v>2B_\infty$, and Sections 5 to 7 hold without $(\mathrm H_\infty)$, in $\mathcal V_\infty$. $(\mathrm H_\infty)$ enters in Section 8, where it makes $\mathcal V_\infty=\mathcal V$, that is $2B_\infty=1$, so that the unconditional analysis reaches the line $\operatorname{Re}v=1$. Without it ($B_\infty>\tfrac12$), the analysis only works in $\operatorname{Re}v>2B_\infty$, which does not reach that line. The opening of Section 3, immediately after Theorem 3.1, explains the limit of Lemma 2.3. Its finite set depends on the distance from the boundary line, so the lemma gives no uniform bound on the number or heights of pairs as $x$ approaches the line.

### Equation (5): $J_{ab}$

The paper defines, for $a,b\in\Sigma$ and $v\in\mathcal V$,
$$J_{ab}(v)=\int_a^{v-b}\mathcal K(z,v)\,dz\tag{5}$$
along the straight segment, and notes that on it the real part lies between $\operatorname{Re}a\le1<\operatorname{Re}v$ and $\operatorname{Re}v-\operatorname{Re}b\in[\operatorname{Re}v-1,\operatorname{Re}v)$, so inside $(0,\operatorname{Re}v)$; hence $J_{ab}$ is single-valued and holomorphic on all of $\mathcal V$, with no hypothesis on the zeros.

The step left out: a segment is convex, so the real part along it lies between the real parts at the ends. At the start, $0<\operatorname{Re}a\le1<\operatorname{Re}v$. At the end, $\operatorname{Re}(v-b)=\operatorname{Re}v-\operatorname{Re}b$ with $0<\operatorname{Re}b\le1$, so in $[\operatorname{Re}v-1,\operatorname{Re}v)$, and $\operatorname{Re}v-1>0$. Both ends are in the strip $0<\operatorname{Re}z<\operatorname{Re}v$ where (K1) says $\mathcal K$ is holomorphic, so the whole segment is. A holomorphic integrand on a segment whose endpoint moves holomorphically gives a holomorphic function of $v$.

### Equation (6), $X_x$ and $M_x$

The paper defines
$$X_x(v)=\sum_{a+b=x}c(a)c(b)J_{ab}(v),\qquad M_x=2\pi iX_x,\tag{6}$$
and states that $X_x$ is holomorphic on $\mathcal V$ and $X_x(x)=0$. Each $J_{ab}$ is holomorphic on that domain, and Lemma 2.3 makes the sum finite. At the collision every segment collapses to a point. The multiple $M_x$ is the holomorphic function added in a full logarithmic turn.

### Equation (7), the derivative at a collision

Since $\partial_vJ_{ab}(a+b)=\mathcal K(a,a+b)$, the paper gives
$$X_x'(x)=\sum_{a+b=x}c(a)c(b)\mathrm B(a,b)\ (G),\qquad X_x'(x)=\tfrac12\sum_{a+b=x}c(a)c(b)K\Bigl(\frac{a-b+3}4\Bigr)\ (S).\tag{7}$$

The steps. $X_x(x)=0$ because at $v=x=a+b$ each segment runs from $a$ to $x-b=a$, which has length zero. For the derivative, differentiate an integral whose upper limit and integrand both depend on $v$ (Leibniz rule):
$$\partial_vJ_{ab}(v)=\mathcal K(v-b,v)\cdot\frac{d(v-b)}{dv}+\int_a^{v-b}\partial_v\mathcal K(z,v)\,dz.$$
At $v=a+b$ the integral is over a point and vanishes, and $\mathcal K(v-b,v)=\mathcal K(a,a+b)$. For $G$, $\mathcal K(a,a+b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)=\mathrm B(a,b)$. For $S$, $\tfrac12K((2a-(a+b)+3)/4)=\tfrac12K((a-b+3)/4)$. In the variable $s=(v-1)/2$, $d/ds=2\,d/dv$, which cancels the $\tfrac12$.

The paper's main terms at $x=1+u$ with $u\ne1$: the pairs $(1,u)$ and $(u,1)$ give, for $G$,
$$c(1)c(u)\{\mathrm B(1,u)+\mathrm B(u,1)\}=-c(u)\cdot\frac2u,$$
since $\mathrm B(1,u)=\Gamma(1)\Gamma(u)/\Gamma(1+u)=1/u$; for $S$,
$$\tfrac12c(1)c(u)\Bigl\{K\Bigl(\frac{1-u+3}4\Bigr)+K\Bigl(\frac{u-1+3}4\Bigr)\Bigr\}=-\tfrac12c(u)\Bigl\{K\bigl(1-\tfrac u4\bigr)+K\bigl(\tfrac12+\tfrac u4\bigr)\Bigr\}.$$
The condition $u\ne1$ is needed because at $u=1$, that is $x=2$, the two pairs are the one diagonal pair $(1,1)$, which occurs once. Its contribution to the first sum is $c(1)^2\mathrm B(1,1)=1$, half of what the two-pair formula would give.

What it is for: (7) is the bridge between the two halves. Section 3 proves the right-hand sums are nonzero at many points; Sections 6 to 8 show $X_x$ is the coefficient of the logarithm on every branch, so a nonzero $X_x'(x)$ means $X_x\not\equiv0$, which means non-trivial monodromy at $x$. Compare with $T$: the residue of $T$ at $x$ (Theorem 4.2) is the same sum as (7) for $G$, with $R_aR_b=c(a)c(b)$.

## Lemma 2.4: the bracket for $S$ does not vanish

The paper proves: for non-real $u$, $K(1-\tfrac u4)+K(\tfrac12+\tfrac u4)\ne0$.

The computation, written out. From $K(w)=(1-w)\pi/\sin\pi w$:
$$K(1-x)=\frac{x\pi}{\sin\pi(1-x)}=\frac{\pi x}{\sin\pi x},\qquad K(\tfrac12+x)=\frac{(\tfrac12-x)\pi}{\sin(\tfrac\pi2+\pi x)}=\frac{(\tfrac12-x)\pi}{\cos\pi x}.$$
With $x=u/4$, the sum over a common denominator is
$$\frac{\pi\{x\cos\pi x+(\tfrac12-x)\sin\pi x\}}{\sin\pi x\cos\pi x}.$$
Put $x=\tfrac14+t$, so $t=(u-1)/4$. Using $\cos(\tfrac\pi4+\pi t)=(\cos\pi t-\sin\pi t)/\sqrt2$ and $\sin(\tfrac\pi4+\pi t)=(\cos\pi t+\sin\pi t)/\sqrt2$, the numerator times $\sqrt2$ is
$$(\tfrac14+t)(\cos\pi t-\sin\pi t)+(\tfrac14-t)(\cos\pi t+\sin\pi t)=\tfrac12\cos\pi t-2t\sin\pi t.$$
This vanishes only if $\cot\pi t=4t$ (for non-real $t$, $\sin\pi t\ne0$). Now, for $t=\alpha+i\beta$,
$$\cot\pi t=\frac{\sin2\pi\alpha-i\sinh2\pi\beta}{\cosh2\pi\beta-\cos2\pi\alpha},$$
so $\operatorname{Im}\cot\pi t$ has the sign of $-\beta$, while $\operatorname{Im}4t=4\beta$. For $\beta\ne0$ they have opposite signs, so they cannot be equal. Non-real $u$ means non-real $t$.

What it is for: the main term for $S$ at $1+u$ is $c(u)$ times this bracket. Section 3 needs the main term to be comparable in size to $c(u)$; Lemma 2.4 says the bracket is never zero, and continuity on a compact window gives a positive lower bound.

## Check your understanding

1. Compute $c(1/6)$. 
2. Why is $J_{ab}$ holomorphic on all of $\mathcal V$ even when $a$ is a zero far from the line?
3. Why does Lemma 2.3 need $\operatorname{Re}x>2B_\infty$ rather than $\operatorname{Re}x>1$?

Answers. (1) Only $k=6$ contributes, with $\operatorname{ord}_1\zeta=-1$: $c(1/6)=\mu(6)\cdot(-1)/6=-1/6$, as $\mu(6)=+1$. (2) The segment's real parts stay in $(0,\operatorname{Re}v)$ whatever $a$ and $b$ are; $J_{ab}$ depends only on the endpoints $a$ and $b$ (and the kernel). (3) The proof needs one of $a$, $b$ to lie in the finite set $F_{\eta/2}$; that requires $\operatorname{Re}x$ to exceed $2B_\infty$ by a margin.

# 3. Section 3: non-cancellation near the line

## The section opener

### Theorem 3.1, non-cancellation

The paper begins with the need for nonzero pair sums: a point $x=1+u$ with $u\in\Sigma$ always has the pairs $(1,u)$ and $(u,1)$, but $c(u)$ may vanish, and without RH other pairs may cancel the main term. It then states the section's one result.

Theorem 3.1. Assume $B<1$. For $y\in\mathbb R$ and $\varepsilon>0$, the disc $|x-(1+iy)|<\varepsilon$ contains infinitely many points $x=1+\rho/q$, with $\rho$ a zero on the critical line and $q$ prime, at which
$$\Theta_G(x)=\sum_{a+b=x}c(a)c(b)\mathrm B(a,b)\ne0,\qquad\Theta_S(x)=\sum_{a+b=x}c(a)c(b)K\Bigl(\frac{a-b+3}4\Bigr)\ne0.$$

The paper adds: for $x\in\mathcal X$, (7) gives $\Theta_G(x)=X_x'(x)$ for $G$ and $\Theta_S(x)=2X_x'(x)$ for $S$ (derivative in $v$); Lemma 2.3 gives no uniform cutoff, so the argument does not use it; all it takes from $(\mathrm H_\infty)$ is $B<1$; under $B<1$ alone a point might have infinitely many pairs, so part of the statement is that both sums converge absolutely. Three steps: choose points whose $c(\rho/q)$ is a single term, discard the few points with a low extra pair, show the high pairs are too small.

New symbols: $\Theta_G$, $\Theta_S$ are the two sums over the pairs at $x$. Keep their domain apart from that of $X_x$. Under $B<1$ the paper proves that the sums converge absolutely at the points $x=1+u$ with $0<\operatorname{Re}u\le1$ (Lemma 3.4). The coefficient $X_x$ is a finite sum and is defined only for $x\in\mathcal X$, that is for $\operatorname{Re}x>2B_\infty$, and the identities $\Theta_G(x)=X_x'(x)$ and $\Theta_S(x)=2X_x'(x)$ are stated for those $x$. Under $B<1$ alone the theorem can supply points outside $\mathcal X$; under $(\mathrm H_\infty)$, where $2B_\infty=1$, all its points lie in $\mathcal X$. The factor $2$ for $S$ is the $\tfrac12$ in (7) moved to the other side.

Why "dense": the theorem gives, for every point $1+iy$ of the line and every radius, infinitely many good points inside. So the set of good points accumulates at every point of the line. That is the arithmetic input to Theorems 1.1 and 1.2.

The plan in numbers, for orientation (the proof fixes the constants): with a large parameter $X$, there are about $X^2/\log^2X$ candidate pairs $(\rho,q)$; at most about $X\log X$ have a second representation; at most about $(\log X\log\log X)^2$ have a low extra pair. The main term is at least about $1/X$, the high pairs at most $X^{-2}$. Each comparison wins by a wide margin.

## Section 3.1: single representations

The paper defines a representation of $u$ as a pair $(\rho',k)$ with $\rho'\in\mathcal Z$, $k$ squarefree and $\rho'/k=u$, and notes that by (2), for non-real $u$,
$$c(u)=\sum_{(\rho',k)\text{ representing }u}\frac{\mu(k)m(\rho')}k.$$
If $(\rho,q)$ with $q$ prime is the only representation of $u=\rho/q$, then $c(u)=-m(\rho)/q\ne0$.

The step left out: for non-real $u$, $ku$ is never $1$, so in (2) only zeros contribute, each with $\operatorname{ord}=m$. And $\mu(q)=-1$ for a prime $q$.

## Lemma 3.2: a second representation forces a zero off the line

The paper proves: let $\rho=\tfrac12+i\gamma$ be a zero with $\gamma>0$, $q$ prime, $u=\rho/q$, and $(\rho',k)\ne(\rho,q)$ another representation. Then $\gcd(k,q)=1$, $k<2q$, $k\ne q$ and $\operatorname{Re}\rho'=k/(2q)\ne\tfrac12$. With $\zeta^*=\rho'$ if $k>q$ and $\zeta^*=1-\bar\rho'$ if $k<q$, $\zeta^*$ is a zero with $\operatorname{Re}\zeta^*>\tfrac12$ and $0<\operatorname{Im}\zeta^*<2\gamma$, and the reduced denominator $d$ of $\operatorname{Re}\zeta^*$ is $q$ or $2q$. Conversely $\zeta^*$ determines $q$, and then $(\rho,q)$ is one of at most two pairs.

The steps, in full.

1. $\rho'/k=\rho/q$ gives $\rho'=k\rho/q=\frac k{2q}+i\frac{k\gamma}q$.
2. $\operatorname{Re}\rho'<1$ (no zeros on or right of $\operatorname{Re}=1$) gives $k<2q$.
3. If $q\mid k$ and $k<2q$ then $k=q$, so $\rho'=\rho$, the excluded representation. Hence $q\nmid k$, and as $q$ is prime, $\gcd(k,q)=1$; in particular $k\ne q$ and $\operatorname{Re}\rho'=k/(2q)\ne\tfrac12$.
4. Reflect to the right half. If $k>q$, $\operatorname{Re}\rho'>\tfrac12$ already. If $k<q$, $1-\bar\rho'$ is a zero by (Z1) with real part $1-\frac k{2q}=\frac{2q-k}{2q}>\tfrac12$ and the same imaginary part. Either way $\operatorname{Re}\zeta^*=j/(2q)$ with $j\in\{k,2q-k\}$, $q<j<2q$, and $\operatorname{Im}\zeta^*=k\gamma/q\in(0,2\gamma)$. Since $2q-k\equiv-k\pmod q$, also $\gcd(j,q)=1$.
5. Reduce $j/(2q)$. As $\gcd(j,q)=1$, the only common factor of $j$ and $2q$ can be $2$. For odd $q$: $d=2q$ if $j$ is odd, $d=q$ if $j$ is even. For $q=2$: $2<j<4$ forces $j=3$ and $d=4=2q$.
6. Recover $q$ from $d$: $d$ odd means $d=q$; $d$ even means $d=2q$. (An odd $q$ never gives an even $d$ other than $2q$, and $q=2$ gives $d=4$.)
7. Given $\zeta^*$ and $q$: $\rho'$ is $\zeta^*$ or $1-\bar\zeta^*$ (two choices), each fixes $k=2q\operatorname{Re}\rho'$ and then $\rho=q\rho'/k$. At most two pairs.

A worked example, to see the constraint. Take $q=5$ and suppose $\rho/5=\rho'/k$ with $k=6$ (squarefree, $5<6<10$). Then $\operatorname{Re}\rho'=6/10=3/5$, a zero off the line at real part $0.6$, height $\tfrac65\gamma$. Its real part has reduced denominator $5$, odd, so $q=5$. If instead $k=3$, then $\operatorname{Re}\rho'=3/10$ and $\zeta^*=1-\bar\rho'$ has real part $7/10$, denominator $10$, even, so $q=5$ again.

What it is for: a bad pair $(\rho,q)$ costs a zero off the critical line below height $2X$. There are at most $N(2X)$ zeros of any kind below that height, which is small compared with the supply of pairs.

## The counting set-up before Theorem 3.3

The paper fixes $y>0$, $0<\varepsilon<y$, the window $J=(y-\tfrac\varepsilon2,y+\tfrac\varepsilon2)$, and for $X\ge3$ the integer $M=\lceil2\log X/A_0\rceil$. $\mathcal P(X)$ is the set of pairs $(\rho,q)$ with $\rho=\tfrac12+i\gamma$ a zero, $X/M<\gamma\le X$, $q$ prime, $\gamma/q\in J$. A pair is good if $(\rho,q)$ is the only representation of $\rho/q$. The paper explains: for each zero, the admissible $q$ fill an interval of relative length about $\varepsilon/y$, and (Z5) supplies $\gg\gamma/\log\gamma$ of them; the worst case $\gamma\approx X/M$ gives $\gg X/\log^2X$ per zero; the lower cutoff $X/M$ keeps $q$ large so $\operatorname{Re}u=1/(2q)$ is small; $M$ is of size $\log X$ because the zeros below $X/M$ number about $N(X/M)\approx(X/M)\log X$, and this must stay below $A_0X$.

Why the condition $\gamma/q\in J$: the point $u=\rho/q=\frac1{2q}+i\frac\gamma q$ has imaginary part $\gamma/q$. Putting $\gamma/q$ in the window $J$ around $y$ places $u$ at height near $y$, so $x=1+u$ is near $1+iy$. The real part $1/(2q)$ is small because $q$ is large. So the points land in the target disc.

Why $M\approx\log X$: Hardy–Littlewood gives at least $A_0X$ distinct zeros on the line up to height $X$, but we want them above $X/M$ (to keep $q$ large). The only way to remove those below $X/M$ is to subtract all zeros below $X/M$, at most $N(X/M)\approx\frac{X}{2\pi M}\log X$. For this to be at most half of $A_0X$ we need $M\gtrsim\log X/A_0$. The paper takes $M=\lceil2\log X/A_0\rceil$. The price: the smallest $\gamma$ is about $X/\log X$, so the number of primes per zero is about $(X/\log X)/\log X$.

## Theorem 3.3: many points with a single representation

The paper proves: there are $c_2>0$ and $X_0$, depending on $y,\varepsilon$, such that for $X\ge X_0$:

(a) $|\mathcal P(X)|\ge c_2X^2/\log^2X$, and at most $4X\log(2X)$ pairs in $\mathcal P(X)$ are not good;

(b) for a good pair, $u=\rho/q$ has $|u-iy|<\varepsilon$, $\operatorname{Re}u=1/(2q)$, $c(u)=-m(\rho)/q$, $|c(u)/u|=m(\rho)/|\rho|\ge1/(X+1)$, and $q\ll_{y,\varepsilon}X$;

(c) distinct pairs give distinct $u$.

### Part (a), the steps

Zeros. The distinct zeros on the line with $X/M<\gamma\le X$ number at least $N_0(X)-N(X/M)$: start with all distinct zeros on the line up to $X$ and remove at most all zeros, of any kind, up to $X/M$. By (Z4), $N_0(X)\ge A_0X$. By (Z2), $N(t)\le t\log t$ for large $t$ (the main term is $\frac t{2\pi}\log\frac t{2\pi}$), so $N(X/M)\le(X/M)\log X\le\tfrac12A_0X$ by the choice of $M$. Hence at least $\tfrac12A_0X$ zeros.

Primes per zero. $\gamma/q\in J$ means $\gamma/(y+\tfrac\varepsilon2)<q<\gamma/(y-\tfrac\varepsilon2)$. Write the left end as $x$ and the right as $(1+\theta)x$; then $1+\theta=(y+\tfrac\varepsilon2)/(y-\tfrac\varepsilon2)$, so $\theta=\varepsilon/(y-\tfrac\varepsilon2)$, a fixed positive number. Since $\gamma>X/M$, $x>X/(M(y+\tfrac\varepsilon2))$, which tends to infinity. (Z5) gives at least $\theta x/(2\log x)$ primes, and $x\gg X/\log X$, $\log x\le\log X+O_{y,\varepsilon}(1)$, so at least $\gg X/\log^2X$.

Multiply: $|\mathcal P(X)|\ge\tfrac12A_0X\cdot cX/\log^2X$.

Bad pairs. A pair that is not good has a second representation; Lemma 3.2 attaches to it a zero $\zeta^*$ with $0<\operatorname{Im}\zeta^*<2\gamma\le2X$, and each $\zeta^*$ serves at most two pairs. The number of zeros with height in $(0,2X)$ is at most $N(2X)\le2X\log(2X)$ for large $X$. So at most $4X\log(2X)$ bad pairs.

The paper adds a further point. The zeros $\zeta^*$ may lie arbitrarily close to the critical line, so $(\mathrm H_\infty)$, which only limits zeros at a fixed distance to its right, gives no bound on their number. The count uses only the total $N(2X)$ from (Z2). So Theorem 3.3 assumes neither $(\mathrm H_\infty)$ nor $B<1$. (Its proof cites (Z2), (Z4) and (Z5) directly, and (Z1) through Lemma 3.2.)

### Parts (b) and (c)

(b) $u=\frac1{2q}+i\frac\gamma q$. Then $|\operatorname{Im}u-y|<\frac\varepsilon2$ because $\gamma/q\in J$, and $\operatorname{Re}u=\frac1{2q}<\frac\varepsilon2$ once $q$ is large, which it is since $q>x\to\infty$. So $|u-iy|\le\operatorname{Re}u+|\operatorname{Im}u-y|<\varepsilon$. The single representation gives $c(u)=-m(\rho)/q$, and
$$\Bigl|\frac{c(u)}u\Bigr|=\frac{m(\rho)/q}{|\rho|/q}=\frac{m(\rho)}{|\rho|}\ge\frac1{|\rho|}\ge\frac1{X+1},$$
since $|\rho|\le\tfrac12+\gamma\le X+1$. Finally $q<\gamma/(y-\tfrac\varepsilon2)\le X/(y-\tfrac\varepsilon2)$.

(c) $\operatorname{Re}u=1/(2q)$ gives $q$, then $\operatorname{Im}u=\gamma/q$ gives $\gamma$, and $\rho=\tfrac12+i\gamma$.

What it is for: (a) supplies far more good points than anything later can spoil; (b) gives the main-term size; (c) lets the near-pair step count spoiled points by counting spoiling pairs.

## Section 3.2: high pairs, and Lemma 3.4

The paper explains first: at $x=1+u$, every pair other than $(1,u)$, $(u,1)$ has $a,b\ne1$, so $\operatorname{Re}a,\operatorname{Re}b\le B$ by Lemma 2.1(ii), hence $\operatorname{Re}a=1+\operatorname{Re}u-\operatorname{Re}b>1-B$, and likewise for $b$. A point of $\Sigma\setminus\{1\}$ with real part above $1-B$ is $1/k$ or $\rho/n$ with denominator at most $n_0=\lfloor1/(1-B)\rfloor$, so Lemma 2.1(iii) applies with $1-B$ in place of $\varepsilon$.

The step left out on denominators: a point $\rho/n$ has real part below $1/n$, and $1/k$ has real part $1/k$; real part above $1-B$ forces $n<1/(1-B)$. This is where $B<1$ is used: it keeps $1-B$ positive, so the extra pairs live in a strip $\operatorname{Re}>1-B$ bounded away from $0$, with bounded denominators, whatever $u$ is. The gain is uniformity. For a fixed $u$ with $\operatorname{Re}u>0$ one has $\operatorname{Re}a=1+\operatorname{Re}u-\operatorname{Re}b\ge\operatorname{Re}u$ even without $B<1$, because $\operatorname{Re}b\le1$; that already bounds the denominators and gives a logarithmic bound on $c(a)$, but with constants that depend on $\operatorname{Re}u$. $B<1$ gives bounds that hold uniformly as $\operatorname{Re}u\downarrow0$, which the points of Theorem 3.3, with $\operatorname{Re}u=1/(2q)$, require.

Lemma 3.4. Assume $B<1$ and let $Y>0$. There is $H_0\ge2Y+2$ such that for all $u$ with $0<\operatorname{Re}u\le1$, $|\operatorname{Im}u|\le Y$, and all $H\ge H_0$,
$$\sum_{\substack{a+b=1+u,\ a,b\ne1\\|\operatorname{Im}a|>H}}|c(a)c(b)\mathrm B(a,b)|\le e^{-H},\qquad\sum_{\substack{a+b=1+u,\ a,b\ne1\\|\operatorname{Im}a|>H}}\Bigl|c(a)c(b)K\Bigl(\frac{a-b+3}4\Bigr)\Bigr|\le e^{-H};$$
in particular both full sums at $1+u$ converge absolutely.

### The steps

Heights. Put $t=\operatorname{Im}a$. Then $\operatorname{Im}b=\operatorname{Im}u-t$, so $|t|-Y\le|\operatorname{Im}b|\le|t|+Y$.

Coefficients and counts. Lemma 2.1(iii) with $\varepsilon=1-B$: $|c(a)|\ll\log(|t|+3)$, $|c(b)|\ll\log(|t|+Y+3)$, so $|c(a)c(b)|\ll\log^2(|t|+Y+3)$. The number of admissible $a$ with $|\operatorname{Im}a|\in[j,j+1]$ is $O(\log(j+4))$. Each $a$ fixes $b=1+u-a$, so counting $a$ counts pairs.

The $G$ kernel. Both real parts lie in $(1-B,B]$, which is contained in the compact interval $[1-B,B]\subset(0,1]$, so (Z6) applies with $x_1=1-B$, $x_2=B$:
$$|\Gamma(a)|\ll(1+|t|)e^{-\pi|t|/2},\qquad|\Gamma(b)|\ll(1+|t|+Y)e^{-\pi(|t|-Y)/2}.$$
Multiply: $\ll(1+|t|+Y)^2e^{-\pi(2|t|-Y)/2}$. The factor $1/\Gamma(1+u)$ is bounded because $1+u$ lies in the compact set $1\le\operatorname{Re}\le2$, $|\operatorname{Im}|\le Y$, and $1/\Gamma$ is entire. With $Y$ fixed and the $\log^2$ absorbed, each term is $\ll(1+|t|)^4e^{-\pi|t|}$.

The $S$ kernel. Put $w=(a-b+3)/4$.

- Real part: $\operatorname{Re}a$, $\operatorname{Re}b\in(1-B,B]$, so $|\operatorname{Re}a-\operatorname{Re}b|<B-(1-B)=2B-1<1$, and $\operatorname{Re}w=(\operatorname{Re}a-\operatorname{Re}b+3)/4\in(\tfrac12,1)$.
- Imaginary part: $\operatorname{Im}w=(t-\operatorname{Im}b)/4=(2t-\operatorname{Im}u)/4$, so $|\operatorname{Im}w|\ge\tfrac12|t|-\tfrac14Y$.
- $|\sin\pi w|\ge\sinh\pi|\operatorname{Im}w|$, from $|\sin(\alpha+i\beta)|^2=\sin^2\alpha+\sinh^2\beta$.
- $|1-w|\le\tfrac12+|\operatorname{Im}w|$, and for $|\operatorname{Im}w|\ge1$, $\sinh\pi|\operatorname{Im}w|\ge\tfrac12(1-e^{-2\pi})e^{\pi|\operatorname{Im}w|}$. So
$$|K(w)|=\frac{\pi|1-w|}{|\sin\pi w|}\le\frac{2\pi}{1-e^{-2\pi}}(1+|\operatorname{Im}w|)e^{-\pi|\operatorname{Im}w|}\le7(1+|\operatorname{Im}w|)e^{-\pi|\operatorname{Im}w|},$$
as $2\pi/(1-e^{-2\pi})\approx6.30$.
- $|t|>H\ge2Y+2$ gives $|\operatorname{Im}w|\ge(Y+1)-\tfrac14Y\ge1$, so the bound applies.
- $e^{-\pi|\operatorname{Im}w|}\le e^{\pi Y/4}e^{-\pi|t|/2}$, so each term is $\ll(1+|t|)^3e^{-\pi|t|/2}$.

Summing. Over $|t|>H$, with $O(\log(j+4))$ points per unit window,
$$\sum_{j\ge H}\log(j+4)(1+j)^4e^{-\pi j/2}\ll(H+3)^5e^{-\pi H/2}.$$
Since $\pi/2>1$, $(H+3)^5e^{-\pi H/2}\le e^{-H}$ once $H$ is large; that fixes $H_0$. The slower kernel ($S$) controls the threshold; the $G$ sum is smaller.

Absolute convergence. The pairs with $|\operatorname{Im}a|\le H_0$ have $a$ in the compact set $1-B\le\operatorname{Re}\le1$, $|\operatorname{Im}|\le H_0$, inside $\operatorname{Re}z>0$, where $\Sigma$ is finite by Lemma 2.1(ii). Finitely many terms plus a convergent tail.

The paper adds that $e^{-H}$ is chosen for convenience: any exponential rate would do with $H$ a multiple of $\log X$, since the near-pair count stays polylogarithmic. The value used is $H=2\log X$, so $e^{-H}=X^{-2}$; and because the lemma gives the same bound $e^{-H}$ for both kernels, the far pairs fall below the main terms, of size $\gg1/X$, for both.

What it is for: it puts a uniform cutoff on how much the high pairs can contribute, independent of where $u$ sits in the window. That uniformity is exactly what Lemma 2.3 cannot give.

## Section 3.3: proof of Theorem 3.1

The paper reduces to $y>0$ and $0<\varepsilon<\min(y,1)$, puts $Y=y+1$ and $H=2\log X\ge H_0$, and for a good pair sets $u=\rho/q$, $x=1+u$. The sum at $x$ splits into the two main pairs, the near pairs (height at most $H$) and the far pairs (above $H$). The main term is about $1/X$, the far pairs at most $X^{-2}$, and the near pairs are counted, not estimated: the points where any occur are thrown away. The paper credits the main-against-far comparison to Bhowmik and Schlage-Puchta and the main-pair isolation with Gamma decay to Egami and Matsumoto, with the near-pair count replacing their condition on ordinates.

### The reductions

Conjugation: $c(\bar a)=c(a)$ (Lemma 2.1(i)), $\mathrm B(\bar a,\bar b)=\overline{\mathrm B(a,b)}$ and $K(\bar w)=\overline{K(w)}$ (Gamma has real values on the reals). The pairs at $\bar x$ are the conjugates of the pairs at $x$, so $\Theta(\bar x)=\overline{\Theta(x)}$, and a good point in the disc about $1+iy$ conjugates to one in the disc about $1-iy$. For $y=0$, any disc about $1$ contains a smaller disc about $1+iy'$ with small $y'>0$. The condition $\varepsilon<y$ keeps the disc $|u-iy|\le\varepsilon$ off the real axis (needed for Lemma 2.4); $\varepsilon<1$ and $Y=y+1$ keep $|\operatorname{Im}u|<Y$ so Lemma 3.4 applies. Also $\operatorname{Re}u=1/(2q)\le\tfrac14\le1$.

### Main terms

For $\Theta_G$: $-2c(u)/u$, of modulus $2m(\rho)/|\rho|\ge2/(X+1)$ by Theorem 3.3(b).

For $\Theta_S$: $c(1)c(u)\{K(\frac{4-u}4)+K(\frac{u+2}4)\}=-c(u)\{K(1-\tfrac u4)+K(\tfrac12+\tfrac u4)\}$. The bracket is continuous on the closed disc $|u-iy|\le\varepsilon$ (both arguments of $K$ have real part in $(0,2)$ there) and nonzero by Lemma 2.4, so on that compact set its modulus has a positive minimum $\lambda$. With $|c(u)|\ge1/q$ and $q\ll X$, the main term is at least $\lambda/q\gg1/X$.

### Near pairs

A good pair is near-bad if $x$ has a pair $(a,b)$ other than the main two with $|\operatorname{Im}a|\le H$. Then $|\operatorname{Im}b|\le H+Y$, and both $a$ and $b$ lie in the set of points of $\Sigma\setminus\{1\}$ with real part above $1-B$ and height at most $H+Y$. With denominators at most $n_0$, (Z2) bounds that set by $\ll(H+Y)\log(H+Y)$ points. So there are $\ll((H+Y)\log(H+Y))^2$ possible pairs $(a,b)$. Each determines $u=a+b-1$, and by Theorem 3.3(c) $u$ determines the pair $(\rho,q)$. With $H=2\log X$, at most $\ll(\log X\log\log X)^2$ good pairs are near-bad.

This is the step that replaces a hypothesis on ordinates. Earlier work had to assume a hypothesis on additive relations among ordinates; here the paper has so many chosen points ($\gg X^2/\log^2X$) that the polylogarithmically many low pairs cannot hit them all, and it simply discards the ones they hit.

### Far pairs

For a good pair that is not near-bad, every non-main pair has $|\operatorname{Im}a|>H$. Lemma 3.4 bounds their total by $e^{-H}=e^{-2\log X}=X^{-2}$. For large $X$, $X^{-2}<2/(X+1)$ and $X^{-2}<\lambda/q$. A sum of modulus less than the main term cannot cancel it, so $\Theta_G(x)\ne0$ and $\Theta_S(x)\ne0$. Exact coincidences among far pairs are harmless, whatever their number or signs.

### Conclusion

Good pairs number at least $c_2X^2/\log^2X-4X\log(2X)\ge\tfrac12c_2X^2/\log^2X$ for large $X$; removing $\ll(\log X\log\log X)^2$ near-bad ones leaves a number tending to infinity. The resulting points are distinct by Theorem 3.3(c) and lie in the disc since $|x-(1+iy)|=|u-iy|<\varepsilon$.

## The remark closing Section 3: why the critical line and the count

The paper says in its unnumbered closing remark that the denominator step for non-vanishing of $c(\rho/p)$ is in Titchmarsh's account of the theorem of Landau and Walfisz, whom he credits, and needs no zeros on the critical line: the term $-m(\rho)/p$ is the only one with denominator divisible by $p$, for $\operatorname{Re}\rho\ge\tfrac12$ and $p\nmid m(\rho)$, and $p$ is chosen large so that $p>m(\rho)$. So non-vanishing alone is classical and needs no count. The far-pair comparison needs the lower bound $|c(u)|\ge1/q$; a sum of several terms could have a denominator as large as the least common multiple of many $k<2q$, which would not beat $X^{-2}$. A single representation gives the bound without further cancellation estimates; that is why the paper uses the critical line, where single-term points come with the count of Theorem 3.3(a). The remark ends by pointing, for comparison, to Lemma 1 of Bhowmik and Schlage-Puchta's 2007 paper on natural boundaries of Dirichlet series.

The denominator step, written out: $c(\rho/p)=\sum\mu(k)m(\rho')/k$ over representations $\rho'/k=\rho/p$. A representation needs $\operatorname{Re}\rho'=k\operatorname{Re}\rho/p<1$, so $k<p/\operatorname{Re}\rho\le2p$. A squarefree $k<2p$ divisible by $p$ is $p$ itself. So all terms except $-m(\rho)/p$ have denominators prime to $p$; their sum is $A/D$ with $p\nmid D$. Then $c(\rho/p)=-m(\rho)/p+A/D=(-m(\rho)D+pA)/(pD)$, and the numerator is $\equiv-m(\rho)D\not\equiv0\pmod p$ when $p\nmid m(\rho)$. So $c\ne0$. But its size can be as small as $1/(pD)$, with $D$ up to the lcm of many integers below $2p$, which is roughly $e^{2p}$. Against a far-pair total of $X^{-2}$ that is useless; hence the need for single representations.

## Check your understanding

1. Why does a second representation of $\rho/q$ have to be off the critical line?
2. Where does the paper use that $\rho$ is on the critical line, and where does it use $q$ prime?
3. If the far pairs decayed only like $e^{-|t|/10}$, what would change?

Answers. (1) Its real part is $k/(2q)$, which equals $\tfrac12$ only for $k=q$, the original representation. (2) The critical line gives $\operatorname{Re}\rho'=k/(2q)$ exactly, which makes the denominator argument of Lemma 3.2 work, and (Z4) counts zeros there. Primality of $q$ gives $\mu(q)=-1$, the $\gcd$ step $q\nmid k\Rightarrow\gcd(k,q)=1$, and the recovery of $q$ from $d$. (3) Choose $H$ a larger multiple of $\log X$, say $H=30\log X$; the near-pair count is still a power of $\log X$, so nothing else changes. The paper says this after Lemma 3.4.

# 4. Section 4: the meromorphic series $T$

## The section opener

The paper says this section proves Theorem 1.1. Since $Q$ is single-valued, moving the contour in (4) across poles produces residues and nothing else; $T$ continues meromorphically, every point of $\Pi$ is at worst a simple pole with residue equal to the sum over pairs, and Section 3 supplies dense points where that residue is nonzero. Everything before the last proof holds without $(\mathrm H_\infty)$. The contour shift parallels Egami and Matsumoto's proof (their Theorem 2.1) for the $\Lambda$-weighted series under RH; Bhowmik and Schlage-Puchta state the half-plane $\operatorname{Re}s>2\sigma_0$ for that series under their Conjecture 2 and say the proof runs parallel. In the paper's reading the argument for $T$ follows theirs with $Q$ in place of $-\zeta'/\zeta$. The differences: $Q$ has poles at scaled zeros, and the contour stops at $\operatorname{Re}w=c$, so finitely many residues appear and right-hand poles cross the contour.

Read this section as the template for Sections 5 to 8. The same two families of singular points appear, the same contour sits between them, and the same thing happens when a right point crosses the line. The difference is that for $T$ crossing leaves a residue, a single term; for $G$ and $S$ it leaves a logarithm.

## Theorem 4.1: the continuation of $T$

The paper proves: $T$ continues to a single-valued meromorphic function on $\operatorname{Re}s>2B_\infty$, with $T(\bar s)=\overline{T(s)}$; its poles are simple and lie in $\Pi$. More precisely, with $0<\delta<\tfrac12(1-B_\infty)$, $F=F_\delta$, and $c\in(B_\infty+2\delta,1)$ not equal to any $\operatorname{Re}a$, $a\in F$: for $\sigma=\operatorname{Re}s>c+B_\infty+2\delta$ with $\sigma\ne c+\operatorname{Re}a$, the theorem gives the following formula.

### Equation (8), the continuation formula

$$T(s)=I_c(s)+\sum_{a\in F}\bigl([\operatorname{Re}a>c]+[\sigma-\operatorname{Re}a<c]\bigr)R_aK_s(a)Q(s-a),\tag{8}$$
where $I_c(s)=\frac1{2\pi i}\int_{(c)}K_s(w)Q(w)Q(s-w)\,dw$ is holomorphic there and $[A]$ is $1$ if $A$ holds, $0$ otherwise.

New symbols. $F=F_\delta$ is the finite set of Lemma 2.1(ii): $1$ and the finitely many zeros with real part above $B_\infty+\delta$. $[A]$ is an indicator (Iverson bracket). $g_s(w)=K_s(w)Q(w)Q(s-w)$ is the integrand. Left points are $a\in\Sigma$ (poles of $Q(w)$); right points are $s-b$, $b\in\Sigma$ (poles of $Q(s-w)$).

The paper's explanation before the proof: a left point crossing the contour leaves a residue, and so does a right point; $w\mapsto s-w$ swaps the families; the contour is placed once, so the first indicator does not depend on $s$; a right point $s-b$ crosses whenever $\sigma$ passes $c+\operatorname{Re}b$, and the second indicator switches on then; only points of $F$ can ever cross, since every other point of $\Sigma$ has real part at most $B_\infty+\delta<c$, and its mirror point $s-b$ has real part at least $\sigma-B_\infty-\delta>c$.

How to read (8). The term for $a\in F$ is counted $0$, $1$ or $2$ times: once if the left point $a$ is right of the line, $\operatorname{Re}a>c$ (it always is for $a=1$, since $c<1$), and once more if the right point $s-a$ has crossed to the left of the line. The residue at a left point $a$ is $R_aK_s(a)Q(s-a)$; the residue at a right point $s-b$, taken with the orientation that arises, is $R_bK_s(b)Q(s-b)$, the same expression with $a$ renamed $b$. That symmetry is why one sum with a two-part indicator covers both.

### Step 1: $\sigma>2$

The paper takes $c_0\in(1,\sigma-1)$ so (4) holds on $\operatorname{Re}w=c_0$, notes that in $c\le\operatorname{Re}w\le c_0$ the only poles are left points $a\in F$ with $\operatorname{Re}a>c$, bounds the horizontal segments by $h^Ae^{-\pi h}$, and applies the residue theorem.

Filled in. Right points have $\operatorname{Re}(s-b)=\sigma-\operatorname{Re}b\ge\sigma-1>c_0$, so they are right of the strip. Left points have $\operatorname{Re}a\le1<c_0$; those in the strip with $\operatorname{Re}a>c$ are in $F$. The rectangle with vertical sides on $\operatorname{Re}w=c_0$ and $\operatorname{Re}w=c$ and horizontal sides at heights $\pm h$, traversed counterclockwise, gives (see the primer, "Cauchy's theorem, the residue theorem, and contour shifts")
$$\int_{c_0-ih}^{c_0+ih}-\int_{c-ih}^{c+ih}+(\text{horizontal sides})=2\pi i\sum_{a\in F,\ \operatorname{Re}a>c}\operatorname{Res}_{w=a}g_s.$$
On the horizontal sides $|K_s(w)|\ll h^Ae^{-\pi h}$, $|Q(w)|\ll\log h$ by Lemma 2.2 (as $\operatorname{Re}w\ge c>B_\infty+2\delta$), and $Q(s-w)$ is bounded since $\operatorname{Re}(s-w)\ge\sigma-c_0>1$. So they vanish as $h\to\infty$. The residue at $a$: $Q$ has residue $R_a$ there and the rest of the integrand is holomorphic, giving $R_aK_s(a)Q(s-a)$. Dividing by $2\pi i$: $T(s)=I_c(s)+\sum_{\operatorname{Re}a>c}R_aK_s(a)Q(s-a)$, which is (8) with every second indicator $0$ (since $\sigma-\operatorname{Re}a\ge\sigma-1>c$).

### Step 2: $I_c$ is holomorphic

No left point is on the line (those in $F$ by the choice of $c$, the others have real part below $c$). A right point on the line would have $\operatorname{Re}b=\sigma-c>B_\infty+2\delta$, so $b\in F$ and $\sigma=c+\operatorname{Re}b$, which is excluded. For large $|t|$, $w=c+it$ and $s-w$ both have real part above $B_\infty+2\delta$, so Lemma 2.2 bounds both $Q$ factors by $\log|t|$, and $K_s$ decays exponentially uniformly in $s$ on compacts. An integrable majorant uniform in $s$ makes the integral holomorphic (see the primer, "Cauchy's theorem, the residue theorem, and contour shifts", which also covers parameter integrals).

### Step 3: crossing a line $\sigma=c+\operatorname{Re}b_1$

The paper takes $b_1\in F$ with $\operatorname{Re}b_1>B_\infty+2\delta$, the set $F_1$ of points of $F$ with the same real part, a point $s_1$ on the line $\operatorname{Re}s_1=c+\operatorname{Re}b_1$, and a small $\epsilon$ (with four conditions listed in the paper). It replaces, for each $b\in F_1$, the segment of $\operatorname{Re}w=c$ within $2\epsilon$ of height $\operatorname{Im}s_1-\operatorname{Im}b$ by a semicircle of radius $2\epsilon$ about $s_1-b$ bulging into $\operatorname{Re}w\le c$. Call the new contour $\mathcal L'$ and $I'(s)=\frac1{2\pi i}\int_{\mathcal L'}g_s$, holomorphic on the disc $|s-s_1|<\epsilon$. For $\sigma>\operatorname{Re}s_1$, $s-b$ is right of $\operatorname{Re}w=c$ and $I'=I_c$. For $\sigma<\operatorname{Re}s_1$, $s-b$ is inside the half-disc, and $I'=I_c+\sum_{b\in F_1}R_bK_s(b)Q(s-b)$. The indicator of $b$ rises by one on that side, so (8) is one meromorphic function on the whole disc.

Why $I'$ is holomorphic on the disc: as $s$ moves in the disc, $s-b$ moves within distance $\epsilon$ of $s_1-b$, so it stays within the full radius-$\epsilon$ disc about $s_1-b$, away from the modified contour, and never touches $\mathcal L'$. The contour separates the right point from the line's left side throughout.

The sign, worked out. Near $w=s-b$, put $z=s-w$; then $Q(s-w)=Q(z)\approx R_b/(z-b)=R_b/(s-b-w)=-R_b/(w-(s-b))$. So $\operatorname{Res}_{w=s-b}g_s=-R_bK_s(s-b)Q(s-b)$, and $K_s(s-b)=\Gamma(s-b)\Gamma(b)/\Gamma(s)=K_s(b)$. When $s-b$ is left of the line, $\mathcal L'$ passes to its left and the straight line to its right. Going up $\mathcal L'$ and back down the straight line circles the point clockwise, so
$$\int_{\mathcal L'}g_s-\int_{(c)}g_s=-2\pi i\operatorname{Res}_{w=s-b}g_s=2\pi i\,R_bK_s(b)Q(s-b).$$
Dividing by $2\pi i$ gives the paper's formula.

Consistency across the line. On the side $\sigma<\operatorname{Re}s_1$, (8) reads $I_c+\{\text{terms, with the indicator of }b\text{ raised by one}\}$. Substituting $I_c=I'-R_bK_s(b)Q(s-b)$ gives $I'+\{\text{terms with the indicators of the side }\sigma>\operatorname{Re}s_1\}$. On the side $\sigma>\operatorname{Re}s_1$, $I_c=I'$ and the same expression results. So one formula, holomorphic plus finitely many meromorphic terms, holds on the whole disc.

### Step 4: assembly

Each term $R_aK_s(a)Q(s-a)$ is meromorphic on $\sigma>\operatorname{Re}a$: $K_s(a)=\Gamma(a)\Gamma(s-a)/\Gamma(s)$ is holomorphic there, $Q(s-a)$ is meromorphic for $\operatorname{Re}(s-a)>0$ with simple poles at $s=a+b$, $b\in\Sigma$. The domain is inside that half-plane:
$$\sigma>c+B_\infty+2\delta>2B_\infty+4\delta\ge1+4\delta>\operatorname{Re}a.$$
Steps 2 and 3 give local meromorphic expressions that agree on overlaps (identity theorem), so a meromorphic function on $\sigma>c+B_\infty+2\delta$, equal to $T$ for $\sigma>2$. Poles are at most simple: $I_c$ or $I'$ is holomorphic, and each of the finitely many terms has at most a simple pole at any point; several terms with a pole at the same point add, and may cancel (Theorem 4.2 computes the total). Letting $c\downarrow B_\infty+2\delta$ and $\delta\downarrow0$ reaches every point of $\sigma>2B_\infty$. Symmetry: $T(\bar s)=\overline{T(s)}$ holds on $\sigma>2$ (real coefficients) and extends by the identity theorem.

A remark on the choice $c<1$. Since $c<1$, the left point $a=1$ is always right of the line, and its term $R_1K_s(1)Q(s-1)=Q(s-1)/(s-1)$ is always present (as $R_1=1$, $K_s(1)=\Gamma(s-1)/\Gamma(s)=1/(s-1)$). This term carries the candidate poles at $1+u$, $u\in\Sigma$, the main pairs of Section 3. It has a pole at $1+u$ only when $c(u)\ne0$, and other terms of (8) can have poles at the same point, so $1+u$ is a pole of $T$ exactly when the total residue of Theorem 4.2 is not zero.

## Theorem 4.2: the residue

The paper proves: for $\operatorname{Re}s_0>2B_\infty$, $s_0$ has finitely many pairs. The residue sums their contributions.

### Equation (9), the residue formula

$$\operatorname{Res}_{s=s_0}T=\sum_{a+b=s_0}R_aR_b\mathrm B(a,b)=\sum_{a+b=s_0}c(a)c(b)\mathrm B(a,b).\tag{9}$$

The steps. If $B_\infty=1$, then $\operatorname{Re}s_0>2$, $T$ is holomorphic there and no pair exists ($\operatorname{Re}(a+b)\le2$). Otherwise choose $\delta$ below both $\frac{1-B_\infty}2$ and $\frac{\operatorname{Re}s_0-2B_\infty}4$, and $c$ with $B_\infty+2\delta<c<\min(1,\operatorname{Re}s_0-B_\infty-2\delta)$ and $c\ne\operatorname{Re}a$, $c\ne\operatorname{Re}s_0-\operatorname{Re}a$ for $a\in F$. These make $s_0$ lie in the domain of (8) ($\operatorname{Re}s_0>c+B_\infty+2\delta$) and off every crossing line, so near $s_0$ the indicators are constants
$$\nu(x)=[\operatorname{Re}x>c]+[\operatorname{Re}s_0-\operatorname{Re}x<c].$$

The residue of one term at $s_0$: $I_c$ contributes nothing. The term $\nu(x)R_xK_s(x)Q(s-x)$ has residue $\nu(x)R_xK_{s_0}(x)R_{s_0-x}$, since $Q(s-x)$ has residue $R_{s_0-x}$ at $s=s_0$ (zero if $s_0-x\notin\Sigma$ or not a pole). And $K_{s_0}(x)=\Gamma(x)\Gamma(s_0-x)/\Gamma(s_0)=\mathrm B(x,s_0-x)$. So
$$\operatorname{Res}_{s_0}T=\sum_{x\in F}\nu(x)R_xR_{s_0-x}\mathrm B(x,s_0-x).$$

Matching with pairs. Every pair $(a,b)$ at $s_0$ has a member in $F$, since $\operatorname{Re}a+\operatorname{Re}b>2B_\infty+4\delta$ forces one real part above $B_\infty+2\delta$. Three cases:

- $a\ne b$, both in $F$. The sum has a term for $x=a$ (the ordered pair $(a,b)$) and for $x=b$ (the pair $(b,a)$), with the same value by symmetry of $R_aR_b\mathrm B(a,b)$. Their weights add to $\nu(a)+\nu(b)=[\operatorname{Re}a>c]+[\operatorname{Re}b<c]+[\operatorname{Re}b>c]+[\operatorname{Re}a<c]=2$, since neither real part equals $c$. The target (9) has the two ordered pairs, also weight $2$.
- $a\in F$, $b\notin F$. Then $\operatorname{Re}b\le B_\infty+\delta<c$, and $\operatorname{Re}a=\operatorname{Re}s_0-\operatorname{Re}b>c$ by the upper bound on $c$. So $\nu(a)=1+1=2$, and there is no term for $x=b$. Again weight $2$ for the two ordered pairs.
- $a=b$. $\nu(a)=[\operatorname{Re}a>c]+[\operatorname{Re}a<c]=1$, matching the single diagonal pair.

What it is for: it identifies the residue with $\Theta_G$, the sum Section 3 controls, independently of the auxiliary choices in (8).

## The proof of Theorem 1.1

The paper: under $(\mathrm H_\infty)$, $2B_\infty=1$ and $B<1$, so $T$ is meromorphic on $\operatorname{Re}s>1$ by Theorem 4.1; Theorem 3.1 gives infinitely many $x$ with $\Theta_G(x)\ne0$ in every disc about a point of the line; by Theorem 4.2 they are poles; and a meromorphic function on a disc about $1+iy$ agreeing with $T$ would have poles accumulating at $1+iy$, a point of its own domain. The paper adds that the conclusion applies to every meromorphic continuation of $T$ to $\operatorname{Re}s>1$, since by the identity theorem there is only one.

The points from Theorem 3.1 are $x=1+\rho/q$; they lie in $\Pi$ (as $1\in\Sigma$ and $\rho/q\in\Sigma$) and in $\operatorname{Re}s>1$. Their residue (9) equals $\Theta_G(x)$ because $R_aR_b=(-c(a))(-c(b))=c(a)c(b)$.

## Check your understanding

1. In (8), why is the term for $a=1$ always present?
2. Why does the residue at a right point come out with a plus sign in $I'$, although the residue of $Q(s-w)$ at $w=s-b$ is $-R_b$?
3. In Theorem 4.2, where is $c\ne\operatorname{Re}s_0-\operatorname{Re}a$ used?

Answers. (1) $c<1=\operatorname{Re}1$, so $[\operatorname{Re}1>c]=1$. (2) The detour passes the point clockwise relative to the straight line, which contributes another minus sign. (3) It keeps $s_0$ off the crossing lines $\sigma=c+\operatorname{Re}a$, so the indicators are constant near $s_0$.

# 5. Section 5: fixed sheets for $G$ and $S$

## The section opener

The paper says this section builds a single-valued object that stands in for $G$ or $S$ below $\operatorname{Re}v=2$, where the series diverge. With $P$ in place of $Q$ the integrand is multivalued. Instead of pushing the contour along a path while continuing the integrand, which is hard to control near the line where singular points accumulate, the paper fixes a direction, cuts along parallel rays from all singular points, and gets a single-valued branch of $P$ and one contour integral with a fixed integrand. For $\operatorname{Re}v>2$ it is the series. The resulting sheet is one branch; Section 7 gets the others by turning the direction. The construction is the additive, infinite-contour form of Hadamard's; Borel has the deformation without cuts. Sections 5 to 7 hold without $(\mathrm H_\infty)$, in $\mathcal V_\infty$; under $(\mathrm H_\infty)$, $\mathcal V_\infty=\mathcal V$.

The model to keep in mind is $\log z$. On the plane cut along the negative real axis it is single-valued; each choice of cut gives one branch; turning the cut changes the branch on the region swept, by $2\pi i$. The paper does the same thing at once for infinitely many logarithmic points, and then for an integral built from them.

One caution on "gets the others by turning the direction". Rotation is the rule for passing between fixed sheets: two sheets at one base point differ by a sum of functions $M_x$ (Theorem 7.3). A germ reached along a path may have changed sheet many times, so it is a sheet plus an accumulated integer combination of the $M_x$, and for $S$ plus a constant $C$ picked up on excursions out of the strip; the paper computes an excursion that adds $4\pi^2$ (Theorem 7.4). The paper does not claim that every member of that family is reached.

## Section 5.1: directions, heights, and equation (10)

The paper fixes a real slope $\kappa$ and $e=(1+i\kappa)/|1+i\kappa|=e^{i\theta}$, $|\theta|<\pi/2$. For $w\in\mathbb C$, $\operatorname{Im}(w/e)$ is its height and $\operatorname{Re}(w/e)$ its abscissa; a $\kappa$-line is a set of constant height; east is increasing abscissa. On a $\kappa$-line,
$$w'\text{ is east of }w\iff\operatorname{Re}w'>\operatorname{Re}w,\tag{10}$$
because $\cos\theta>0$.

What this is: rotate the plane by $-\theta$ (divide by $e$). Then $\kappa$-lines become horizontal lines, height is the vertical coordinate and abscissa the horizontal one. In the original plane a $\kappa$-line is a line of slope $\kappa$, direction $e$. East along it means moving in direction $+e$, which is to the right and (for $\kappa>0$) up.

Why (10) holds: two points on one $\kappa$-line differ by a real multiple of $e$, $w'-w=te$. Then $\operatorname{Re}(w'-w)=t\cos\theta$, and $\cos\theta>0$, so $t>0$ exactly when $\operatorname{Re}w'>\operatorname{Re}w$. This lets the paper compare positions along a $\kappa$-line using ordinary real parts, which is how most later comparisons are made.

### Generic slopes

The paper calls $\kappa$ generic if no two distinct points of $\Sigma$, and no two distinct points of $\Pi$, lie on one $\kappa$-line, and says all but countably many $\kappa$ are generic. Genericity lets the collisions at a candidate point be treated one at a time. The horizontal direction $\kappa=0$ fails: the points $1/k$ all lie on the real axis, and a zero $\rho$ off the line has the same imaginary part as $1-\bar\rho$.

Why countably many: $\Sigma$ and $\Pi$ are countable. Two distinct points lie on a common line of exactly one slope (or a vertical line, which no finite $\kappa$ gives). So the bad slopes are one per pair of points, a countable set.

### $\operatorname{Log}_\kappa$

The paper puts $\operatorname{Log}_\kappa(y)=i\theta+\operatorname{Log}(y/e)$, with cut $y\in-e[0,\infty)$, and says it agrees with the principal logarithm on $\operatorname{Re}y>0$.

The check: $\operatorname{Log}$ (principal) has its cut on $(-\infty,0]$, so $\operatorname{Log}(y/e)$ has its cut where $y/e\le0$, that is $y\in-e[0,\infty)$, the ray pointing west from $0$. For $\operatorname{Re}y>0$, $\arg y\in(-\tfrac\pi2,\tfrac\pi2)$, and $\arg(y/e)=\arg y-\theta\in(-\pi,\pi)$ since $|\theta|<\tfrac\pi2$. So $\operatorname{Log}(y/e)=\log|y|+i(\arg y-\theta)$, and adding $i\theta$ gives $\log|y|+i\arg y=\operatorname{Log}y$.

### The cut domain $U_\kappa$ and the branch $P^\kappa$

The paper lets $\ell_a=(a-e[0,\infty))\cap\{\operatorname{Re}z>0\}$ be the westward ray from $a\in\Sigma$, and $U_\kappa$ the half-plane $\operatorname{Re}z>0$ minus all these rays. It shows $U_\kappa$ is open (only finitely many rays meet a compact set), contains $\operatorname{Re}z>1$, and that each of its points flows east into $\operatorname{Re}z>1$ without meeting a cut; hence $U_\kappa$ is simply connected, and $-Q$ has a primitive there. $P^\kappa$ is the primitive equal to $P$ on $\operatorname{Re}z>1$.

The steps left out:

- Openness. A ray meeting a compact set $K\subset\{\operatorname{Re}z>0\}$ starts at $a$ with $\operatorname{Re}a\le1$ and runs west, so $\operatorname{Re}a\ge\min_K\operatorname{Re}z$; and the ray can only meet $K$ if $a$ is within bounded distance of $K$ (the ray's height is fixed and it only moves west). So $a$ lies in a compact subset of $\operatorname{Re}z>0$, where $\Sigma$ is finite. Finitely many closed rays have closed union, so removing them leaves an open set.
- $\operatorname{Re}z>1$ contains no cut point, since every ray starts at real part at most $1$ and goes west.
- No cut eastward. If the eastward ray $z+te$ ($t\ge0$) hit $\ell_a$ at $z+te=a-se$, then $z=a-(s+t)e$ would lie on $\ell_a$, so $z\notin U_\kappa$.
- Simply connected. Push any loop in $U_\kappa$ east, every point by the same $te$; by the previous point it stays in $U_\kappa$, and for large $t$ it lies in $\operatorname{Re}z>1$, which is convex, where it shrinks to a point. So every loop is contractible (see the primer, "Hadamard and Borel's cut-and-contour construction: the sheet $D^\kappa$", for the primitive $P^\kappa$; simple connectivity itself is standard complex analysis). On a simply connected domain every holomorphic function has a primitive.

So $P^\kappa(z)=P(z_0)-\int_{z_0}^zQ(\xi)\,d\xi$ along any path in $U_\kappa$ from a point $z_0$ with $\operatorname{Re}z_0>1$. Different $\kappa$ give different cuts and so possibly different values at the same $z$.

## Lemma 5.1: $P^\kappa$ near a singular point and at large height

The paper proves: (a) if $a$ is the only point of $\Sigma$ on its $\kappa$-line, then for small $R$, on the disc $|z-a|<R$ minus $\ell_a$, $P^\kappa(z)=c(a)\operatorname{Log}_\kappa(z-a)+E_a(z)$ with $E_a$ holomorphic on the whole disc. (b) For $\eta>0$ there are $t_1$, $C$ with $|P^\kappa(z)|\le C\log(|\operatorname{Im}z|+2)$ for $\operatorname{Re}z\ge B_\infty+2\eta$, $|\operatorname{Im}z|\ge t_1$.

Part (a), filled in. $Q$ has residue $R_a=-c(a)$ at $a$, so $(P^\kappa)'=-Q$ has the form $c(a)/(z-a)+(\text{holomorphic})$ on the disc. The function $c(a)\operatorname{Log}_\kappa(z-a)$ has derivative $c(a)/(z-a)$ and its cut is exactly $z-a\in-e[0,\infty)$, the ray $\ell_a$. So $P^\kappa-c(a)\operatorname{Log}_\kappa(z-a)$ has holomorphic derivative on the slit disc; it is single-valued there, and its derivative extends holomorphically across the slit, so it extends too: that is $E_a$. Why the hypothesis "only point on its $\kappa$-line": a point $a'$ east of $a$ on the same $\kappa$-line sends its westward ray $\ell_{a'}$ straight through $a$, so the disc minus $\ell_a$ would still be cut by $\ell_{a'}$ and the formula would fail. Points on other $\kappa$-lines have rays at a positive distance from $a$, so a small enough disc misses them.

The coefficient $c(a)$ is also the jump across the cut: going once counterclockwise round $a$ changes $\operatorname{Log}_\kappa(z-a)$ by $2\pi i$, so $P^\kappa$ changes by $2\pi ic(a)$. This is the number that later multiplies through to $2\pi iX_x$.

Part (b), filled in. A cut meets $\operatorname{Re}z\ge B_\infty+2\eta$ only if it starts at real part at least $B_\infty+2\eta$, that is from a point of $F_\eta$, a finite set. Each such ray, cut off at $\operatorname{Re}z=B_\infty+2\eta$, is a bounded segment, so above some height none is present. For such large $|t|$ the horizontal segment from $x+it$ to $2+it$ avoids every cut, and
$$P^\kappa(x+it)=P(2+it)+\int_x^2Q(\xi+it)\,d\xi$$
(because $(P^\kappa)'=-Q$, integrating from $x$ to $2$ gives $P^\kappa(2+it)-P^\kappa(x+it)=-\int_x^2Q$). $|P(2+it)|\le P(2)$, and Lemma 2.2 bounds $|Q(\xi+it)|$ by $C\log|t|$ on the segment, which has length at most $2$. For $x\ge2$, $|P^\kappa|\le P(2)$ directly.

What it is for: (a) is the local shape that produces the logarithm in Section 6; (b) is the growth bound that, with the kernel decay (K2), makes the sheet's integral converge.

## Section 5.2: separating graphs

The paper says the sheet will be the integral of $\mathcal K(z,v)P^\kappa(z)P^\kappa(v-z)$, whose integrand is holomorphic at $z$ when $z$ is on no cut $\ell_a$, $v-z$ is on no cut $\ell_b$, and $0<\operatorname{Re}z<\operatorname{Re}v$. (A cut with $c(a)=0$ is artificial but avoided like the others.) The second condition: $v-z\in\ell_b$ means $z=v-b+te$, $t\ge0$, so $z$ is at or east of $v-b$ on its $\kappa$-line. Hence the contour must pass, $\kappa$-line by $\kappa$-line, east of every left point $a$ and west of every right point $v-b$. On a $\kappa$-line carrying both, this needs the right point strictly east of the left one, and fails exactly when $v$ lies on the westward ray from $a+b$. So the cuts for the sheet are westward rays from the points of $\Pi$.

The geometry, step by step. $v-z=b-te$ ($t\ge0$) rearranges to $z=(v-b)+te$: the right point's cut, seen in the $z$-plane, points east. So in $z$ every left point carries a westward cut and every right point an eastward cut. A contour running upward (increasing height) must cross each $\kappa$-line at one point, east of all left points and west of all right points on that line. If on some line the right point $v-b$ sits at or west of a left point $a$, the cuts overlap and no crossing point exists. $v-b=a-te$ is $v=(a+b)-te$, so the forbidden $v$ form the westward ray from $a+b$.

### $L_x$ and $\Omega_\kappa$

The paper defines, for $x\in\mathcal X$, $L_x=(x-e[0,\infty))\cap\mathcal V_\infty$, and $\Omega_\kappa=\mathcal V_\infty$ minus all $L_x$. It is open (finitely many $L_x$ meet a compact set, by Lemma 2.3 and $\operatorname{Re}x\le2$) and connected (from a point with $\operatorname{Re}v\le2$, go east until $\operatorname{Re}v=\tfrac52$, staying in $\Omega_\kappa$; the region $\operatorname{Re}v>2$, or $2<\operatorname{Re}v<3$ for $S$, has no cuts and is connected).

$\Omega_\kappa$ plays for the sheet the role $U_\kappa$ plays for $P^\kappa$: a cut domain on which the sheet is single-valued. The cuts start at the candidate points $x$, which is where Section 6 finds the logarithms.

### Separating $\kappa$-graphs

The paper defines a separating $\kappa$-graph for $v$: a piecewise linear curve $\Gamma$ that is a graph of abscissa over height, with real parts in a compact subset of $(0,\operatorname{Re}v)$, equal for large $|\operatorname{Im}z|$ to a vertical line $\operatorname{Re}z=c$ with $B_\infty<c<\operatorname{Re}v-B_\infty$, and with every $a\in\Sigma$ strictly west of $\Gamma$ on its $\kappa$-line and every right point $v-b$ strictly east. $\Gamma$ is oriented by increasing height (upward on the tails). Each condition has a job: a graph over height meets each $\kappa$-line once, so "west of $\Gamma$" makes sense; compact real parts keep $\mathcal K$ holomorphic; the tails right of $B_\infty$ on both sides are where Lemma 5.1(b) applies. If $\Gamma$ separates and $z\in\Gamma$, then $z$ and $v-z$ lie in $U_\kappa$.

"Graph of abscissa over height": in rotated coordinates (height vertical, abscissa horizontal) $\Gamma$ is the graph of a function abscissa $=\alpha(\text{height})$. A vertical line $\operatorname{Re}z=c$ is such a graph, since it crosses each tilted $\kappa$-line once; in rotated coordinates it looks slightly tilted, as Figure 1's caption says. Orientation on the tails: for $z=c+iy$, height $=\operatorname{Im}((c+iy)e^{-i\theta})=y\cos\theta-c\sin\theta$, increasing in $y$.

Why the tail conditions $B_\infty<c<\operatorname{Re}v-B_\infty$: on the tail, $\operatorname{Re}z=c$ and $\operatorname{Re}(v-z)=\operatorname{Re}v-c$, and Lemma 5.1(b) needs both real parts above $B_\infty$ (by a margin $2\eta$) to bound $P^\kappa(z)$ and $P^\kappa(v-z)$ by a logarithm.

## Lemma 5.2: a separating graph exists exactly off the cuts

The paper proves: for $v\in\mathcal V_\infty$ a separating $\kappa$-graph exists if and only if $v\in\Omega_\kappa$.

The "only if" direction. If $v=x-te$ with $t\ge0$ and $x=a+b$, then $v-b=a-te$ is at or west of $a$ on one $\kappa$-line, and no curve can pass strictly east of $a$ and strictly west of $v-b$ on that line.

The "if" direction, step by step.

1. Room on every line. If $a$ and $v-b$ share a $\kappa$-line, then $v-b$ is strictly east of $a$. Two cases: if $\operatorname{Re}(a+b)\le2B_\infty$, then $\operatorname{Re}(v-b-a)=\operatorname{Re}v-\operatorname{Re}(a+b)>0$ since $\operatorname{Re}v>2B_\infty$, and (10) says east; otherwise $a+b\in\mathcal X$, and $v-b$ at or west of $a$ would put $v$ on $L_{a+b}$, which is excluded.
2. The midline. Take $c=\operatorname{Re}v/2$ and $\eta$ with $4\eta<\operatorname{Re}v-2B_\infty$, so $c>B_\infty+2\eta$. A left point with $\operatorname{Re}a\ge c$ has $\operatorname{Re}a>B_\infty+\eta$, so $a\in F_\eta$. A right point with $\operatorname{Re}(v-b)\le c$ has $\operatorname{Re}b\ge\operatorname{Re}v/2>B_\infty+\eta$, so $b\in F_\eta$. Only finitely many points are on the wrong side of the midline, and they lie on finitely many $\kappa$-lines.
3. Tents. On each of those lines pick a point strictly between the eastmost left point and the westmost right point, with real part in $(0,\operatorname{Re}v)$ (possible by step 1). This wording, which is the paper's, is shorthand: a line may carry points of one family only, and then one of the two extreme points does not exist. In that case the family that is present gives one bound, and the requirement that the real part lie in $(0,\operatorname{Re}v)$ gives the other. Let $\Gamma$ be $\operatorname{Re}z=c$ outside thin disjoint bands around these lines, and inside each band a tent (two line segments) up to the chosen point.
4. No collateral damage. The bands are thin enough to contain no other relevant point: near the finitely many lines there are only finitely many left points with real part above a small $\varepsilon_1$, and finitely many right points with real part below $\operatorname{Re}v-\varepsilon_1$ (local finiteness in a bounded region). Left points with real part below $\varepsilon_1$ and right points with real part above $\operatorname{Re}v-\varepsilon_1$ are on the correct side automatically, by (10), as long as $\Gamma$'s real parts stay in $[\varepsilon_1,\operatorname{Re}v-\varepsilon_1]$.
5. Outside the bands, a left point with $\operatorname{Re}a<c$ is west of the midline on its $\kappa$-line by (10), and a right point with $\operatorname{Re}(v-b)>c$ is east.

The tails are on $\operatorname{Re}z=c=\operatorname{Re}v/2$, which satisfies $B_\infty<c<\operatorname{Re}v-B_\infty$.

Figure 1 in Section 6 shows the tents used in constructing such a graph. It also shows the flat top at a collision, which is removed and replaced by an arc in the local calculation.

## Theorem 5.3: the sheet

For $v\in\Omega_\kappa$ the theorem defines the sheet by a separating contour.

### Equation (11), the sheet integral

$$D^\kappa(v)=\frac1{2\pi i}\int_\Gamma\mathcal K(z,v)P^\kappa(z)P^\kappa(v-z)\,dz\tag{11}$$
with $\Gamma$ any separating $\kappa$-graph for $v$. The value does not depend on $\Gamma$; $D^\kappa$ is holomorphic on $\Omega_\kappa$; and $D^\kappa=D$ on $\Omega_\kappa\cap\{\operatorname{Re}v>2\}$.

### Independence of the graph

The conditions are convex in the abscissa function: on each $\kappa$-line the admissible abscissae form an interval (east of the eastmost left point, west of the westmost right point, real part in the allowed range), so if graphs with abscissae $\alpha_0$ and $\alpha_1$ separate, so does the graph with abscissa $(1-t)\alpha_0+t\alpha_1$, $0\le t\le1$. On the tails, a vertical line $\operatorname{Re}z=c$ has, at each height, abscissa affine in $c$, so the combination of tails at $c_0$ and $c_1$ is the vertical line at $(1-t)c_0+tc_1$, still in the allowed interval $(B_\infty,\operatorname{Re}v-B_\infty)$. The paper spells out two more points: on a $\kappa$-line the real part is an increasing affine function of the abscissa, by (10), so each condition confines the abscissa to an open interval or half-line and their intersection is an interval; and a convex combination of two graphs whose real parts lie in compact subsets of $(0,\operatorname{Re}v)$ has real parts in the convex hull of their union, again a compact subset of $(0,\operatorname{Re}v)$. This gives a homotopy of separating graphs, inside the open set where the integrand is holomorphic. Cauchy's theorem applied to the region between two graphs, cut off at large height, gives equal integrals once the short connecting segments at the top and bottom are shown to vanish: there $\mathcal K$ decays like $e^{-\pi|\operatorname{Im}z|/2}$ by (K2), and both $P^\kappa$ factors grow at most like $\log|\operatorname{Im}z|$ by Lemma 5.1(b).

### Holomorphy in $v$

Fix $v_1$ and a graph $\Gamma$ for it with tails on $\operatorname{Re}z=c$, and $\eta>0$ with $B_\infty+2\eta<\min(c,\operatorname{Re}v_1-c)$. For $v$ near $v_1$, the same $\Gamma$ still separates:

- left points do not depend on $v$;
- right points $v-b$ with small $\operatorname{Re}b$ have real part near $\operatorname{Re}v$, larger than every real part on $\Gamma$, so stay east by (10);
- right points at heights where $\Gamma$ is vertical have $\operatorname{Re}(v-b)\ge\operatorname{Re}v-B_\infty-\eta>c$ unless $b\in F_\eta$;
- the remaining finitely many right points had a positive margin at $v_1$, which survives a small move.

So near $v_1$ the sheet is one integral over a fixed contour of an integrand holomorphic in $v$. On the tails $\operatorname{Re}z=c$ and $\operatorname{Re}(v-z)$ are both at least $B_\infty+2\eta$, so the integrand is dominated uniformly by (K2) times $\log^2$. Differentiation under the integral sign gives holomorphy (see the primer, "Cauchy's theorem, the residue theorem, and contour shifts", which also covers parameter integrals).

### Agreement with the series

For $\operatorname{Re}v>2$ the straight line $\operatorname{Re}z=c$ with $1<c<\operatorname{Re}v-1$ separates: every left point has $\operatorname{Re}a\le1<c$, every right point $\operatorname{Re}(v-b)\ge\operatorname{Re}v-1>c$. On it $P^\kappa(z)=P(z)$ and $P^\kappa(v-z)=P(v-z)$, as both arguments have real part above $1$. So (11) is (3).

The paper closes the section: for fixed $v$ the tails sit a fixed distance right of $B_\infty$, only finitely many zeros lie further east, the bounds depend on $v$, and every later use of them is local in $v$.

What the section achieves: for each slope $\kappa$, a holomorphic function $D^\kappa$ on the cut domain $\Omega_\kappa$ that equals the series where the series converges. It is the continuation of the series along any path that stays in $\Omega_\kappa$. No path-by-path continuation was needed.

## Check your understanding

1. Why does $\kappa=0$ fail even under RH?
2. Why must every cut point the same way (west)?
3. In Lemma 5.2, what goes wrong if $v$ lies on $L_x$ for some $x=a+b$?

Answers. (1) The points $1/k$, $k$ squarefree, all lie on the real axis, so many points of $\Sigma$ share a horizontal line. (2) So that the cut domain is simply connected by a single eastward flow, and so that left cuts (west) and right cuts (east, after $z\mapsto v-z$) can be separated line by line. (3) On that $\kappa$-line the right point $v-b$ is at or west of the left point $a$; their cuts overlap and no contour can pass between them.

# 6. Section 6: one collision and the local logarithm

## The section opener

The paper asks what a sheet looks like near a point $x\in\mathcal X$ and answers: a logarithm times the coefficient $X_x$ of (6), plus a function holomorphic at $x$. The reason: the contour is pinched at $x$ between $a$ and $v-b$ for every pair at $x$; with a generic direction these pinches lie on different $\kappa$-lines and can be isolated; the contour away from the pinches gives a holomorphic function of $v$; each pinch is a short arc on which both factors are explicit logarithms, and a one-variable calculation gives $c(a)c(b)\operatorname{Log}_\kappa(v-x)J_{ab}(v)$ plus a holomorphic function. Summing the arcs gives one term per pair.

A one-dimensional model, to see where a logarithm times an integral comes from. Consider
$$\Phi(\epsilon)=\frac1{2\pi i}\int f(t)\operatorname{Log}t\operatorname{Log}(\epsilon-t)\,dt$$
along a short arc passing between $0$ and $\epsilon$. As $\epsilon\to0$ the two singular points $0$ and $\epsilon$ squeeze the arc. Differentiating in $\epsilon$ turns one logarithm into $1/(\epsilon-t)$, a simple pole; pushing the arc across it picks up $f(\epsilon)\operatorname{Log}\epsilon$. Integrating back in $\epsilon$ gives $\operatorname{Log}\epsilon\int_0^\epsilon f$ plus something holomorphic. That is the whole calculation; the rest of the proof sets it up and checks the orientation.

## Theorem 6.1: the local model

The paper proves: let $x\in\mathcal X\cap\mathcal V$ and $\kappa$ generic. There is $r>0$ such that the disc $|v-x|<r$ minus $L_x$ lies in $\Omega_\kappa$. The sheet has the following form on that slit disc.

### Equation (12), the local logarithm

$$D^\kappa(v)=\operatorname{Log}_\kappa(v-x)\,X_x(v)+H(v),\tag{12}$$
with $H$ holomorphic on the whole disc.

Reading (12): $\operatorname{Log}_\kappa(v-x)$ has its cut along $v-x\in-e[0,\infty)$, which is exactly the ray $L_x$; so (12) is a single-valued function on the disc minus $L_x$, as $D^\kappa$ is. Crossing the cut, $\operatorname{Log}_\kappa$ jumps by $2\pi i$, so $D^\kappa$ jumps by $2\pi iX_x(v)=M_x(v)$. Since $X_x(x)=0$, the singularity is mild. Set aside the holomorphic part $H$, whose value at $x$ can be non-zero; what is left is $\operatorname{Log}_\kappa(v-x)X_x(v)$, and there are three cases. If $X_x'(x)\ne0$, then $X_x(v)\approx X_x'(x)(v-x)$ near $x$ and the non-holomorphic part is approximately $X_x'(x)(v-x)\log(v-x)$. If $X_x$ has a zero of order $m>1$ at $x$, the logarithmic term starts at order $m$, like $(v-x)^m\log(v-x)$. If $X_x\equiv0$ there is no logarithmic term and (12) is holomorphic at $x$. In the first two cases $D^\kappa$ is continuous at $x$ but not holomorphic there.

The calculation in Section 6 isolates each collision with a short contour arc. The outer contour passes through the collision points at $v=x$ and separates the other left and right points. After the small pieces around collisions are removed, the rest has enough clearance to stay fixed as $v$ changes near $x$. Its integral is holomorphic there. Each short arc accounts for one ordered pair and yields its own logarithmic term. This explains why the coefficient is a finite sum of pair integrals for two logarithms and a finite sum of kernel values when a logarithm meets a pole.

### The configuration at $v=x$

The paper shows: if $a\in\Sigma$ and $x-b$ lie on one $\kappa$-line, either $\operatorname{Re}(a+b)\le2B_\infty$ and $x-b$ is east of $a$, or $a+b\in\mathcal X$ lies on the $\kappa$-line of $x$ and genericity gives $a+b=x$, so $x-b=a$. Each left-right pair on a $\kappa$-line is strictly ordered or a collision, and each line carries at most one left and one right point.

The steps. In the first case $\operatorname{Re}(x-b)-\operatorname{Re}a=\operatorname{Re}x-\operatorname{Re}(a+b)>0$, so (10) gives east. In the second, $(x-b)-a=x-(a+b)$ is a real multiple of $e$ (two points on one $\kappa$-line), so $x$ and $a+b$ are on one $\kappa$-line; both are in $\Pi$, and a generic $\kappa$ puts no two distinct points of $\Pi$ on one line, so $a+b=x$. At most one left point per line is genericity for $\Sigma$; two right points $x-b$, $x-b'$ on one line would put $b$, $b'$ on one line, again excluded.

A collision is a pair at $x$: the left point $a$ and the right point $x-b$ coincide. Each ordered pair $(a,b)$ at $x$ gives exactly one collision, at the point $a$.

### The outer contour $\Gamma_0$, $\Gamma_{\mathrm{out}}$, and Figure 1

The paper builds a $\kappa$-graph $\Gamma_0$ for $x$ as in Lemma 5.2: tails on $\operatorname{Re}z=\operatorname{Re}x/2$; tents on the finitely many lines with no collision where a detour is needed; at each colliding $a_i$ a flat top through $a_i$ (abscissa constant for heights within $r_0$ of $a_i$'s), joined to the rest by ramps between heights $r_0$ and $2r_0$ from $a_i$'s. $\Gamma_{\mathrm{out}}$ is $\Gamma_0$ minus the open flat tops. The paper chooses $r_0$ to satisfy four conditions. The first three control the geometry: the collision bands of half-width $2r_0$ are disjoint from one another and from the tent bands; the discs $|z-a_i|<2r_0$ are disjoint, meet $\Sigma$ and $x-\Sigma$ only in $a_i$, and carry the expansion of Lemma 5.1(a), and likewise about the $b_i$; within its band no left point is east and no right point west of a flat top or its ramps. The third is possible since only finitely many points compete, independent of $r_0$, and by genericity none but $a_i$ has $a_i$'s height. The fourth is joint holomorphy of $f(t,\mu)=e\,\mathcal K(a_i+et,x+e\mu)$ for $|t|,|\mu|<2r_0$. Here $t$ measures position relative to the fixed left point, and $\mu$ measures the displacement of $v$ from the collision. The calculation differentiates the moving logarithm holding $\mu$ fixed, then puts $\mu$ equal to the actual displacement. Condition (K1) supplies holomorphy because the two real parts of the two inputs $z$ and $v-z$ stay positive and $x$ is in the open kernel domain.

Figure 1 shows this in rotated coordinates (abscissa across, height up, so $\kappa$-lines are horizontal). Panel (a), at $v=x$: filled dots are left points with cuts running west, open dots are right points with cuts running east; the graph has a tent around a non-colliding pair and a flat top through a collision, where a filled and an open dot coincide. Panel (b), at $v=x+\delta$: the right points have moved by $\delta$, $\Gamma_{\mathrm{out}}$ has not, and the arc $A_\epsilon$ replacing the flat top passes east of $a_i$ at $a_i$'s height and west of $a_i+\delta$ at its height. With $\operatorname{Re}\delta<0$ the right point has moved west of the left one, so the arc doubles back.

Why the flat top passes through $a_i$: at $v=x$ the left point $a_i$ and the right point $x-b_i$ coincide, so no graph can separate them. The flat top is a placeholder of fixed shape; it is removed and replaced, for each $v$ near $x$, by an arc that does separate them.

### The radius $r$ and holomorphy of $I_{\mathrm{out}}$

The paper writes $v=x+\delta$, fixes $\eta>0$ with $B_\infty+2\eta<\operatorname{Re}x/2$, notes that beyond a fixed height all points have real part at most $B_\infty+\eta$, so the tails have margin at least $\eta$; on the compact part finitely many points come near the graph, each non-colliding one with a positive margin (its distance from the graph). Left points do not move, right points move by $\delta$, and a point keeps its side while $|\delta|$ is below its margin. It takes $r$ below half the least margin and below half of $\eta$, below $r_0/4$, and small enough that $v$ stays in $\mathcal V_\infty$. Then non-colliding points keep their sides, the moved colliding points $a_i+\delta$ have heights inside the removed bands, $\Gamma_{\mathrm{out}}$ avoids all cuts, and on the tails $\operatorname{Re}z=\operatorname{Re}x/2$ and $\operatorname{Re}(v-z)>\operatorname{Re}x/2-\eta/2$ are above $B_\infty+\eta$, so Lemma 5.1(b) (with $\eta/2$) and (K2) dominate the integrand uniformly. So
$$I_{\mathrm{out}}(v)=\frac1{2\pi i}\int_{\Gamma_{\mathrm{out}}}\mathcal K(z,v)P^\kappa(z)P^\kappa(v-z)\,dz$$
is holomorphic on the whole disc $|v-x|<r$, including on $L_x$ and at $x$.

The arithmetic: $\operatorname{Re}(v-z)$ on a tail is $\operatorname{Re}x+\operatorname{Re}\delta-\operatorname{Re}x/2>\operatorname{Re}x/2-r>\operatorname{Re}x/2-\eta/2$, and $\operatorname{Re}x/2>B_\infty+2\eta$, so it exceeds $B_\infty+\tfrac32\eta$. The height of $a_i+\delta$ differs from $a_i$'s by at most $|\delta|<r_0/4$, inside the flat-top band of half-width $r_0$, so the moved right point is in the part of the contour that has been removed.

The point of $I_{\mathrm{out}}$: it is the part of the sheet that sees no pinch. It is holomorphic on the full disc, so it goes into $H$.

### The arcs

The paper fixes a collision $(a,b)$, and in its disc puts $t=(z-a)/e$ and $\epsilon=\delta/e$. The left point is $t=0$, the right point is $t=\epsilon$, and $\epsilon\notin(-\infty,0]$ when $v\notin L_x$; height is $\operatorname{Im}t$, east is increasing $\operatorname{Re}t$. The arc $A_\epsilon$ runs from $-ir_0$ to $ir_0$, a graph over $\operatorname{Im}t$ with $\operatorname{Re}t>0$ at height $0$ and $\operatorname{Re}t<\operatorname{Re}\epsilon$ at height $\operatorname{Im}\epsilon$: a polygon through a small $\tau>0$ and $\epsilon-\tau$ in height order if $\operatorname{Im}\epsilon\ne0$, or through $\epsilon/2$ if $\epsilon>0$ is real. Then $\Gamma_{\mathrm{out}}$ with the arcs is a separating graph for $v$, so $D^\kappa=I_{\mathrm{out}}+\sum_iI_i$ by Theorem 5.3.

Checks:

- The right point: $v-b=x+\delta-b=a+\delta$, so $t=\delta/e=\epsilon$.
- $v\in L_x$ means $v=x-se$, $s\ge0$, that is $\epsilon=\delta/e\in(-\infty,0]$. Off the cut, $\epsilon$ is not a non-positive real.
- The left point's cut is $t\in(-\infty,0]$ (westward from $0$, at height $0$); the right point's cut is $t\in\epsilon+[0,\infty)$ (eastward from $\epsilon$, at height $\operatorname{Im}\epsilon$). The arc crosses height $0$ at positive real part, east of the left cut, and height $\operatorname{Im}\epsilon$ at real part below $\operatorname{Re}\epsilon$, west of the right cut. So it avoids both.
- The flat top in $t$-coordinates is the segment $\operatorname{Re}t=0$ from $-ir_0$ to $ir_0$, so the arc has the same ends and slots into $\Gamma_{\mathrm{out}}$.

### One arc integral

The paper cites Pham's (Disc 1) and Pérez-Marco's Theorem 1.5 for the local pinch calculation and works out the orientation itself, since their jump conventions differ. On $A_\epsilon$, by Lemma 5.1(a) with constants absorbed,
$$P^\kappa(z)=c(a)\operatorname{Log}t+E_1(t),\qquad P^\kappa(v-z)=c(b)\operatorname{Log}(\epsilon-t)+E_2(\epsilon-t).$$

Where these come from. $\operatorname{Log}_\kappa(z-a)=\operatorname{Log}_\kappa(et)=i\theta+\operatorname{Log}t$ by the definition of $\operatorname{Log}_\kappa$, and the constant $c(a)i\theta$ goes into $E_1$. For the second factor, $v-z=(x+\delta)-(a+et)=b+e(\epsilon-t)$, so Lemma 5.1(a) at $b$ gives $c(b)\operatorname{Log}_\kappa(e(\epsilon-t))+E_b=c(b)\operatorname{Log}(\epsilon-t)+(\text{holomorphic})$. Both expansions need the point alone on its $\kappa$-line, which genericity gives.

The kernel in the new variable is $f(t,\mu)=e\,\mathcal K(a+et,x+e\mu)$, jointly holomorphic (as $\operatorname{Re}a$, $\operatorname{Re}b>0$, so $z$ near $a$ and $v-z$ near $b$ keep $0<\operatorname{Re}z<\operatorname{Re}v$). With $\mu=\epsilon$ and $dz=e\,dt$, $f(t,\epsilon)\,dt=\mathcal K(z,v)\,dz$. The extra variable $\mu$ separates the dependence through the kernel from the dependence through the logarithm.

The four terms. Expand the product:

1. $E_1E_2$: holomorphic integrand on a fixed segment; holomorphic in $\epsilon$.
2. $c(a)\operatorname{Log}t\cdot E_2(\epsilon-t)$: one cut, at $t\le0$. Move the arc to a fixed polygon east of $t=0$; holomorphic in $\epsilon$.
3. $E_1\cdot c(b)\operatorname{Log}(\epsilon-t)$: one cut, eastward from $\epsilon$. Move the arc to a fixed polygon west of every possible $\epsilon$; holomorphic in $\epsilon$.
4. $c(a)c(b)\operatorname{Log}t\operatorname{Log}(\epsilon-t)$: the pinch term, $c(a)c(b)\Phi(\epsilon,\epsilon)$ with
$$\Phi(\epsilon,\mu)=\frac1{2\pi i}\int_{A_\epsilon}f(t,\mu)\operatorname{Log}t\operatorname{Log}(\epsilon-t)\,dt.$$

The derivative in $\epsilon$. Near any $\epsilon$ off the cut, the arc can be held fixed while $\epsilon$ moves a little, so only $\operatorname{Log}(\epsilon-t)$ is differentiated, giving $1/(\epsilon-t)$:
$$\partial_\epsilon\Phi=\frac1{2\pi i}\int_{A_\epsilon}\frac{f(t,\mu)\operatorname{Log}t}{\epsilon-t}\,dt.$$
Now compare with a fixed polygon $A^E$ from $-ir_0$ to $ir_0$ that passes east of every $\epsilon$ in the disc, for example through $-ir_0$, $\tfrac{r_0}2-ir_0$, $\tfrac{r_0}2+ir_0$, $ir_0$. Since $|\epsilon|<r<r_0/4<r_0/2$, every $\epsilon$ is west of $A^E$; and $A^E$ crosses height $0$ at $t=r_0/2$, off the cut of $\operatorname{Log}t$. The integrand's only singularity between $A_\epsilon$ and $A^E$ is the pole at $t=\epsilon$ (both arcs pass east of the cut of $\operatorname{Log}t$). Going up $A_\epsilon$ (west of $\epsilon$) and back down $A^E$ (east of $\epsilon$) circles $\epsilon$ clockwise. The residue of $f\operatorname{Log}t/(\epsilon-t)$ at $t=\epsilon$ is $-f(\epsilon,\mu)\operatorname{Log}\epsilon$, since $1/(\epsilon-t)=-1/(t-\epsilon)$. A clockwise loop gives $-2\pi i$ times the residue, so
$$\frac1{2\pi i}\Bigl(\int_{A_\epsilon}-\int_{A^E}\Bigr)=f(\epsilon,\mu)\operatorname{Log}\epsilon,\qquad\partial_\epsilon\Phi=f(\epsilon,\mu)\operatorname{Log}\epsilon+h(\epsilon,\mu),$$
with $h=\frac1{2\pi i}\int_{A^E}f\operatorname{Log}t/(\epsilon-t)\,dt$ holomorphic in both variables, since $A^E$ is fixed and stays away from every $\epsilon$.

Integrating back. Put $\mathcal P(\epsilon,\mu)=\int_0^\epsilon f(t,\mu)\,dt$ (straight segment). By the product rule,
$$\partial_\epsilon\bigl[\operatorname{Log}\epsilon\cdot\mathcal P\bigr]=\frac{\mathcal P}\epsilon+\operatorname{Log}\epsilon\cdot f(\epsilon,\mu),$$
and $\mathcal P/\epsilon$ is holomorphic because $\mathcal P(0,\mu)=0$ (a holomorphic function vanishing at $0$, divided by $\epsilon$, has a removable singularity). So $\mathcal R=\Phi-\operatorname{Log}\epsilon\cdot\mathcal P$ has
$$\partial_\epsilon\mathcal R=h-\frac{\mathcal P}\epsilon,$$
holomorphic on the whole disc $|\epsilon|<r$, cut and centre included. A function on the slit disc whose derivative extends holomorphically to the full disc extends itself: $\mathcal R(\epsilon,\mu)=\mathcal R(\epsilon_0,\mu)+\int_{\epsilon_0}^\epsilon(h-\mathcal P/\epsilon')\,d\epsilon'$, path-independent on the disc. $\mathcal R(\epsilon_0,\mu)$ is holomorphic in $\mu$ because at fixed $\epsilon_0$ the arc is fixed. So $\mathcal R$ is jointly holomorphic.

Setting $\mu=\epsilon$:
$$\Phi(\epsilon,\epsilon)=\operatorname{Log}\epsilon\cdot\mathcal P(\epsilon,\epsilon)+\mathcal R(\epsilon,\epsilon),\qquad\mathcal P(\epsilon,\epsilon)=\int_0^\epsilon e\,\mathcal K(a+et,v)\,dt=\int_a^{a+\delta}\mathcal K(z,v)\,dz=J_{ab}(v),$$
since $a+\delta=v-b$. Finally $\operatorname{Log}\epsilon=\operatorname{Log}(\delta/e)=\operatorname{Log}_\kappa\delta-i\theta$, and $-i\theta J_{ab}$ is holomorphic. So the arc contributes $c(a)c(b)\operatorname{Log}_\kappa(v-x)J_{ab}(v)$ plus a holomorphic function.

Summing. One collision per ordered pair at $x$, a diagonal pair being one collision. The sum of $c(a)c(b)J_{ab}(v)$ over the pairs is $X_x(v)$ by (6). Everything else ($I_{\mathrm{out}}$, the three non-pinch terms of each arc, the $\mathcal R$'s and the $-i\theta$ terms) is holomorphic on the disc and makes up $H$. The disc minus $L_x$ lies in $\Omega_\kappa$ because a separating graph was built for each such $v$ (Lemma 5.2).

Why the extra variable $\mu$ is needed: $\Phi(\epsilon,\epsilon)$ depends on $\epsilon$ in two places, the logarithm and the kernel. Differentiating the kernel's dependence would produce a second integral with two logarithms, and nothing would simplify. Freezing the kernel's argument as $\mu$, doing the calculation in $\epsilon$ alone, and setting $\mu=\epsilon$ at the end, avoids that.

## The sign check and the form for $S$

When $B_\infty<1$, the paper checks the sign at $x=2$ for $G$. the only pair is $(1,1)$, $c(1)^2=1$, and the leading singular term is $+\delta\log\delta$, matching the prime number theorem heuristic $\int e^{-\delta y}y^{-2}\,dy$. It says the heuristic serves only as a check of the sign and the normalization, and that no proof uses it. For $S$, with $\alpha=(x-1)/2$, $v-x=2(s-\alpha)$, so $\operatorname{Log}_\kappa(v-x)=\operatorname{Log}_\kappa(s-\alpha)+\log2$; the term $\log2\cdot X_x(2s+1)$ is holomorphic, the local model reads $\operatorname{Log}_\kappa(s-\alpha)X_x(2s+1)+$ holomorphic, and $\frac d{ds}X_x(2s+1)$ at $\alpha$ is $\Theta_S(x)$.

The sign check in full. Why $x=2$ has only the pair $(1,1)$: every other point of $\Sigma$ has real part below $1$, so a sum equal to $2$ needs both members to be $1$. Then $X_2(v)=J_{11}(v)=\int_1^{v-1}\mathcal K(z,v)\,dz$, and with $v=2+\delta$, $J_{11}\approx\delta\,\mathcal K(1,2)=\delta\,\Gamma(1)^2/\Gamma(2)=\delta$. So (12) gives $D^\kappa(2+\delta)=\delta\log\delta+\dots$. The heuristic is the paper's, and it is an averaged statement, not an asymptotic for each $n$: $n$ has on average about $n/\log^2n$ ordered representations, so $G(2+\delta)$ behaves like $\sum_nn^{-1-\delta}/\log^2n$; with $n=e^y$, $dn=e^y\,dy$, this is about $I(\delta)=\int_1^\infty e^{-\delta y}y^{-2}\,dy$. Differentiating twice, $I''(\delta)=\int_1^\infty e^{-\delta y}\,dy=e^{-\delta}/\delta\approx1/\delta$, and $(\delta\log\delta)''=1/\delta$. The singular parts agree, with a plus sign.

For $S$: $\log(2w)=\log2+\log w$ holds for $\operatorname{Log}_\kappa$ because multiplying by the positive real $2$ does not change the argument. And $\frac d{ds}X_x(2s+1)=2X_x'(2s+1)$, which at $s=\alpha$ is $2X_x'(x)=\Theta_S(x)$ by the remark after Theorem 3.1.

What the theorem is for: it identifies the monodromy of the sheet at $x$. Going once counterclockwise round $x$ in $v$, on a small loop inside the disc, multiplies nothing and adds $2\pi iX_x(v)$. Section 7 shows this is the same on every branch, and Section 8 uses it to block meromorphic extension.

## Lemma 6.2: the pole–logarithm pinch

The paper introduces the lemma with one paragraph. The residue step in the proof of Theorem 6.1 is needed again in Section 9, for a series in which one factor has a pole to begin with: a pole meeting a logarithm leaves the logarithm times the value of the rest of the integrand at the pole. It compares this with the mixed case of Pham's discontinuity formula, (Disc 4). As in the proof of Theorem 6.1, $t$ is a local coordinate in which the left point is $t=0$ and the right point is $t=\epsilon$, and $\operatorname{Log}$ is the principal logarithm, cut along $(-\infty,0]$.

The paper proves: let $r_0>0$, let $f(t,\mu)$ be holomorphic on $|t|<2r_0$, $|\mu|<2r_0$, let $E_1,E_2$ be holomorphic on $|t|<2r_0$, and let $c_1,c_2\in\mathbb C$. There are $r$ with $0<r<r_0/4$ and a function $H$ holomorphic on $|\epsilon|<r$ such that, for every $\epsilon$ with $|\epsilon|<r$ off $(-\infty,0]$ and every piecewise linear path $A_\epsilon$ from $-ir_0$ to $ir_0$ in $|t|<\tfrac32r_0$ that is a graph over $\operatorname{Im}t$, with $\operatorname{Re}t>0$ at height $0$ and $\operatorname{Re}t<\operatorname{Re}\epsilon$ at height $\operatorname{Im}\epsilon$,
$$\frac1{2\pi i}\int_{A_\epsilon}f(t,\epsilon)\bigl(c_1\operatorname{Log}t+E_1(t)\bigr)\Bigl(\frac{c_2}{\epsilon-t}+E_2(\epsilon-t)\Bigr)dt=c_1c_2\,f(\epsilon,\epsilon)\operatorname{Log}\epsilon+H(\epsilon).$$

Reading the statement. The first bracket is the shape of $P^\kappa$ near a left point (Lemma 5.1(a)): a logarithm with coefficient $c_1$ plus a holomorphic part. The second bracket is the shape of a meromorphic function near a simple pole: residue term plus a holomorphic part. The arc $A_\epsilon$ is the same kind of arc as in Theorem 6.1, east of the left point and west of the right one. One $r$ and one $H$ serve every $\epsilon$ and every such arc; that is what lets Theorem 9.7 use the lemma for all $v$ near a candidate point at once.

The steps.

1. The comparison arc. Take any $r<r_0/4$ and the fixed polygon $A^E$ through $-ir_0$, $\tfrac{r_0}2-ir_0$, $\tfrac{r_0}2+ir_0$, $ir_0$, as in Theorem 6.1. It lies in $|t|<2r_0$ (its corners have modulus $\sqrt5\,r_0/2\approx1.12\,r_0$), off the cut of $\operatorname{Log}t$ (it crosses height $0$ at $t=r_0/2$), and east of every $\epsilon$ with $|\epsilon|<r$.
2. What lies between the arcs. The cut $(-\infty,0]$ is west of $A_\epsilon$, because $A_\epsilon$ crosses height $0$ at positive real part. The point $\epsilon$ is east of $A_\epsilon$ and west of $A^E$ on its own height. So the closed curve "up $A_\epsilon$, down $A^E$" runs clockwise round $t=\epsilon$ and encloses nothing else singular. For $t$ between the arcs, $|t|<\tfrac32r_0$ and $|\epsilon|<\tfrac14r_0$ give $|\epsilon-t|<\tfrac74r_0<2r_0$, so $E_2(\epsilon-t)$ is defined.
3. Expand the product into four terms.
   - $c_1c_2\,f(t,\epsilon)\operatorname{Log}t/(\epsilon-t)$. Simple pole at $t=\epsilon$; since $1/(\epsilon-t)=-1/(t-\epsilon)$ the residue is $-c_1c_2f(\epsilon,\epsilon)\operatorname{Log}\epsilon$. A clockwise loop contributes $-2\pi i$ times the residue, so after dividing by $2\pi i$ the integral over $A_\epsilon$ equals $c_1c_2f(\epsilon,\epsilon)\operatorname{Log}\epsilon$ plus the integral over $A^E$. The latter is holomorphic in $\epsilon$: the contour is fixed and stays at positive distance from the disc of $\epsilon$.
   - $c_2\,f(t,\epsilon)E_1(t)/(\epsilon-t)$. The same pole, with no logarithm: the same argument gives $c_2f(\epsilon,\epsilon)E_1(\epsilon)$ plus an integral over $A^E$, both holomorphic in $\epsilon$.
   - $c_1\,f(t,\epsilon)\operatorname{Log}t\,E_2(\epsilon-t)$ and $f(t,\epsilon)E_1(t)E_2(\epsilon-t)$. Holomorphic between the arcs, so $A_\epsilon$ may be replaced by $A^E$, and the integrals are holomorphic in $\epsilon$.
4. None of the holomorphic pieces depends on $A_\epsilon$. Their sum is $H$.

Compare with Theorem 6.1. There both factors were logarithms, and the paper had to differentiate in $\epsilon$ to turn one of them into a pole, then integrate back; that is why the coefficient came out as an integral, $\int_0^\epsilon f$, which vanishes at $\epsilon=0$. Here the pole is present from the start, the residue theorem applies at once, and the coefficient is the value $f(\epsilon,\epsilon)$, which need not vanish at $\epsilon=0$. No second variable $\mu$ has to be kept separate: the lemma is stated with $f(t,\epsilon)$ directly.

What it is for: Theorem 9.7, the local model for $G_{\log}$.

## Check your understanding

1. Why is the singular part of $D^\kappa$ at $x$ the logarithm times $X_x(v)$, not times the constant $X_x'(x)$?
2. In the one-arc calculation, where is $r<r_0/4$ used?
3. Why does genericity of $\kappa$ matter here?
4. In Lemma 6.2, why is the coefficient of $\operatorname{Log}\epsilon$ a value of $f$ and not an integral of it?

Answers. (1) The arc integral produces $\operatorname{Log}\epsilon\int_0^\epsilon f$, and $\int_0^\epsilon f$ is the full function $J_{ab}(v)$; $X_x'(x)$ is the weighted sum of the derivatives $J_{ab}'(x)$, which is only first-order information. (2) It puts every $\epsilon$ west of the fixed polygon $A^E$, and keeps the moved right points inside the removed bands. (3) It puts each collision on its own $\kappa$-line, alone with its partner, so the pinches can be isolated and Lemma 5.1(a) applies at each $a_i$ and $b_i$. (4) The second factor already has a simple pole at $t=\epsilon$, so the residue theorem evaluates the rest of the integrand, $f(t,\epsilon)\operatorname{Log}t$, at that point.

# 7. Section 7: rotation and every reached branch

## The section opener

The paper says a sheet is one branch, and this section finds which germs are reached by continuing the series along paths and what each looks like at a candidate point. Fix $v_1$ and turn $\kappa$. A direction is critical for $v_1$ if the eastward ray from $v_1$ in that direction passes through a point of $\mathcal X$, equivalently if $v_1$ lies on a cut $L_x$ for that direction. Between critical directions nothing changes; at a critical direction the sheet jumps by the functions $M_x$ of the points on the critical ray; those are holomorphic on all of $\mathcal V$, so no local coefficient changes. The local jump is the pinch monodromy of Pham and Pérez-Marco; here the jumps at all points swept over are collected in one identity, Theorem 7.3.

The picture. Stand at $v_1$ and look east. The cuts $L_x$ point west from each candidate point $x$, all in the direction $-e$. As you turn $\kappa$, the cuts swing. Whenever a cut swings across $v_1$, the sheet at $v_1$ changes, by the jump across that cut. The jump across $L_x$ is $M_x=2\pi iX_x$, by (12).

## Lemma 7.1: no cut crosses, no change

The paper proves: if $v_1\in\Omega_\kappa$ for all $\kappa$ in an interval, the germ of $D^\kappa$ at $v_1$ is constant on it.

The steps. If $\operatorname{Re}v_1>2$, every sheet equals $D$ near $v_1$ (Theorem 5.3). Otherwise fix $\kappa_0$ in the interval. The segment from $v_1$ eastward in direction $\kappa_0$ to $\operatorname{Re}v=\tfrac52$ contains no point of $\mathcal X$ (else $v_1$ would be on that point's cut). Only finitely many $x$ have cuts, for directions near $\kappa_0$, that come near the segment, and each is at positive distance from it; so there is a convex tube about the segment inside $\Omega_\kappa$ for all $\kappa$ near $\kappa_0$. The tube reaches $\operatorname{Re}v>2$, where all these sheets equal $D$; by the identity theorem on the connected tube, they all agree near $v_1$. So the germ is locally constant in $\kappa$, hence constant on the interval (an interval is connected).

## Lemma 7.2: the jump at a critical direction

The paper proves: let $v_1\in\mathcal V_\infty\setminus\mathcal X$, and $x_1,\dots,x_k$ the points of $\mathcal X$ on the open eastward ray from $v_1$ of slope $\kappa$. For generic $\kappa^-<\kappa<\kappa^+$ close to $\kappa$, as germs at $v_1$,
$$D^{\kappa^+}-D^{\kappa^-}=\sum_{i\le k}M_{x_i}.$$

The paper's idea: compare the two sheets along the segment from $v_1$ east to where both are the series; they agree there, and walking west, each $x_i$ on the segment adds $M_{x_i}$, because the two logarithms of Theorem 6.1 at $x_i$ differ by $2\pi i$ west of $x_i$ and by nothing east of it.

The two logarithms, worked out. $\operatorname{Log}_\kappa(y)=i\theta+\operatorname{Log}(y/e)$ takes arguments in $(\theta-\pi,\theta+\pi)$. Let $\theta^-<\theta<\theta^+$ correspond to $\kappa^-<\kappa<\kappa^+$. East of $x_j$ along the segment, $y=v-x_j$ points in direction $e^{i\theta}$, argument $\theta$, inside both ranges: the logarithms agree. West of $x_j$, $y$ points in direction $-e^{i\theta}$, argument $\theta+\pi$ or $\theta-\pi$. Now $\theta+\pi$ lies in the range of $\operatorname{Log}_{\kappa^+}$ (since $\theta<\theta^+$) but not in that of $\operatorname{Log}_{\kappa^-}$ (since $\theta+\pi>\theta^-+\pi$), where the argument is $\theta-\pi$ instead. So
$$\operatorname{Log}_{\kappa^+}(y)-\operatorname{Log}_{\kappa^-}(y)=i(\theta+\pi)-i(\theta-\pi)=2\pi i$$
in the thin sector between the two cuts, which contains the west radius. That is the paper's "the one for $\kappa^+$ being the larger".

The induction. Let $D_*=D^{\kappa^+}-D^{\kappa^-}$, holomorphic near each open piece of the segment between the $x_i$, and $0$ near the east end. Label the $x_i$ from east to west. At $x_j$, (12) for both directions gives $D_*=(\operatorname{Log}_{\kappa^+}-\operatorname{Log}_{\kappa^-})X_{x_j}+(H^+-H^-)$ on a disc. East of $x_j$ that is $H^+-H^-$; west of $x_j$ it is $H^+-H^-+M_{x_j}$. Suppose (induction) that $D_*$ east of $x_j$ equals $\sum_{i<j}M_{x_i}$. That function is holomorphic on all of $\mathcal V$, and $H^+-H^-$ is holomorphic on the disc and equals it on the eastern part, so they are equal on the whole disc. Then west of $x_j$, $D_*=\sum_{i\le j}M_{x_i}$. Continuing to $v_1$ gives the lemma.

The paper notes nothing later depends on the sign of this jump; only that the difference of two sheets is an integer combination of the $M_x$.

## Theorem 7.3: rotation

The paper proves: if $v_1\in\Omega_\kappa\cap\Omega_{\kappa'}$ with $\kappa<\kappa'$, then as germs at $v_1$, $D^{\kappa'}-D^\kappa=\sum_xM_x$, the finite sum over $x\in\mathcal X$ in the open eastward sector at $v_1$ between the two directions.

Why finitely many: points of $\mathcal X$ have real part at most $2$, and the sector between two directions with $|\theta|<\pi/2$, cut off at $\operatorname{Re}v=2$, is a bounded triangle with real parts at least $\operatorname{Re}v_1>2B_\infty$. $\mathcal X$ is locally finite there (Lemma 2.3), so the triangle holds finitely many points, on finitely many critical rays. Between critical slopes use Lemma 7.1; at each critical slope use Lemma 7.2.

## The family $D^\kappa+m+C$

The paper defines $\mathcal M$, the finite integer combinations of the $M_x$, all holomorphic on $\mathcal V$. For $v_1\in\mathcal V_\infty\setminus\mathcal X$, all but countably many $\kappa$ have $v_1\in\Omega_\kappa$, and by Theorem 7.3 the family of germs $D^\kappa+m+C$, $m\in\mathcal M$, $C\in\mathbb C$, does not depend on which such $\kappa$ is used. This family is the candidate for the set of all branches, and the next theorem shows that continuation along paths never leaves it: the family contains every reached germ. The paper says plainly that it does not claim the converse, that every $m\in\mathcal M$ and every constant $C$ is reached from the series, so the family does not classify the monodromy that occurs. The constant $C$ is needed only for $S$, because a path for $S$ may leave the region where sheets are defined; for $G$ it can be taken to be $0$.

Why all but countably many: $v_1$ lies on $L_x$ for exactly one direction per $x$ (the direction from $x$ to $v_1$, if it is westward), and $\mathcal X$ is countable.

Why the family does not depend on $\kappa$: by Theorem 7.3, $D^{\kappa'}=D^\kappa+m_0$ with $m_0\in\mathcal M$, so $D^{\kappa'}+m+C=D^\kappa+(m_0+m)+C$, and $m_0+m\in\mathcal M$.

## Theorem 7.4: every branch

The paper proves:

(a) A germ $D^\kappa+m+C$ continues along every path in $\mathcal V_\infty\setminus\mathcal X$, staying in the family with the same $C$. In particular $G$ continues along every path in $\{\operatorname{Re}v>2B_\infty\}\setminus\Pi$ starting in $\operatorname{Re}v>2$, and each reached germ is $D^\kappa+m$.

(b) For $S$, a germ at a point of $\mathcal V_\infty\setminus\mathcal X$ reached from $\operatorname{Re}v>3$ along a path in $\{\operatorname{Re}v>2B_\infty\}\setminus\Pi$ along which continuation exists has the form $D^\kappa+m+C$.

(c) For $x\in\mathcal X$ and generic $\kappa$ there is a disc $B_x$ about $x$, depending only on $x$ and $\kappa$, such that every germ of the family at a point of $B_x\setminus L_x$ is $\operatorname{Log}_\kappa(v-x)X_x+$ a function holomorphic on $B_x$. So every germ reached as in (a) or (b) at a point of $B_x\setminus L_x$ has the same coefficient $X_x$.

### Part (a)

For each point $p$ of the path choose $\kappa$ with $p\in\Omega_\kappa$ and a disc about $p$ inside $\Omega_\kappa$. A germ of the family at a point of that disc can be written with this $\kappa$ (the family is $\kappa$-independent), and $D^\kappa+m+C$ is holomorphic on the disc. So the germ continues across the disc and stays in the family. Finitely many such discs cover the compact path.

For $G$: $\mathcal V=\{\operatorname{Re}v>1\}$ and $B_\infty\ge\tfrac12$, so $\mathcal V_\infty=\{\operatorname{Re}v>2B_\infty\}$, and $\mathcal V_\infty\setminus\mathcal X=\{\operatorname{Re}v>2B_\infty\}\setminus\Pi$. The starting germ in $\operatorname{Re}v>2$ is $D=D^\kappa$, with $m=0$, $C=0$.

### Part (b): excursions and the constant

The paper explains first. A path for $S$ may leave $\mathcal V$ to the right, into $\operatorname{Re}v\ge3$, where (11) is not available, and come back; the constant $C$ comes from these excursions. In $s=(v-1)/2$,
$$\frac d{ds}J_{ab}(2s+1)=\tfrac12K\Bigl(\frac{s+2-b}2\Bigr)+\tfrac12K\Bigl(\frac{a-s+1}2\Bigr).$$
The second term has a simple pole at $s=a+1$ with residue $-1$, the first a pole of residue $-1$ at $s=b+2$, both beyond $\mathcal V$. If the derivative of the correction $m+C$ has a pole there with non-zero residue, a loop round the point adds $2\pi i$ times that residue, and a path through the point has no continuation. That is why admissibility for $S$ requires a path "along which continuation exists", and for $G$ (whose $J_{ab}$ are holomorphic on the whole half-plane) it need not. When $B_\infty<1$, the paper gives the example $D+M_2$, $M_2=2\pi iJ_{11}$, reached by one positive loop round $s=\tfrac12$, gains $4\pi^2$ on a positive loop round $s=3$, and likewise round $s=2$.

The formula for $\frac d{ds}J_{ab}$, derived. In (5) for $S$, $\mathcal K(z,v)=\tfrac12K(w)$ with $w=(2z-v+3)/4$, so $dz=2\,dw$ and the integrand becomes $K(w)\,dw$. With $v=2s+1$ the limits become $z=a\mapsto w=(2a-2s+2)/4=(a-s+1)/2$ and $z=v-b\mapsto w=(2v-2b-v+3)/4=(s+2-b)/2$. So
$$J_{ab}(2s+1)=\int_{(a-s+1)/2}^{(s+2-b)/2}K(w)\,dw,$$
with $s$ only in the limits. The fundamental theorem of calculus gives the paper's formula: the upper limit contributes $K(\cdot)\cdot\tfrac12$ and the lower contributes $-K(\cdot)\cdot(-\tfrac12)$.

The residues, derived. $K(w)=\Gamma(w)\Gamma(2-w)$ has a pole at $w=0$ with $K(w)\approx\Gamma(2)/w=1/w$, and at $w=2$ with $K(w)\approx1/(2-w)$. In the second term, $w=(a-s+1)/2$ vanishes at $s=a+1$, and $\tfrac12\cdot\frac1w=\frac1{a+1-s}=\frac{-1}{s-(a+1)}$: residue $-1$. In the first, $2-w=(b+2-s)/2$ vanishes at $s=b+2$, and $\tfrac12\cdot\frac1{2-w}=\frac{-1}{s-(b+2)}$: residue $-1$. These points have $\operatorname{Re}s\ge1$, that is $\operatorname{Re}v\ge3$. (Further poles of $K$, at $w=-1,-2,\dots$ and $w=3,4,\dots$, give poles further right in $s$, also beyond $\mathcal V$; and poles at $s=a-3$ or $s=b-2$, far to the left of the region used.)

The worked constant. A term $\omega J_{ab}$ of the correction contributes $\omega\cdot(-1)$ to the residue of its $s$-derivative at $s=b+2$, so a positive loop adds $2\pi i\cdot(-\omega)$. With $\omega=2\pi i$ and $a=b=1$: $-2\pi i\cdot2\pi i=4\pi^2$, at $s=3$ (from $b+2$) and at $s=2$ (from $a+1$).

The proof. Write $\mathsf R=\{\operatorname{Re}v>2\}$ and $\mathsf D=\mathcal V_\infty$. They cover $\{\operatorname{Re}v>2B_\infty\}$, and $\mathsf R\cap\mathsf D=\{2<\operatorname{Re}v<3\}$ lies in every $\Omega_\kappa$, as all cuts have real part at most $2$. On $\mathsf R$ the series $D$ is holomorphic (the series $S$ converges absolutely for $\operatorname{Re}s>\tfrac12$). Subdivide the path so each closed piece lies in $\mathsf R$ or in $\mathsf V$; merge consecutive pieces in the same set; switches then happen in $\mathsf R\cap\mathsf D$. The first piece, starting in $\operatorname{Re}v>3$, is an $\mathsf R$-piece with germ $D$; set $\tilde h=0$.

- On a $\mathsf V$-piece, part (a) keeps the germ in the family.
- At a switch into $\mathsf R$, all sheets equal $D$, so the germ is $D+h$, $h=m+C$.
- Along the $\mathsf R$-piece, subtract the holomorphic $D$ from the continued germ; what remains is a continuation $\tilde h$ of $h$ (it exists because the germ continues, by hypothesis).
- $h'=m'$ is a finite combination of the functions $\frac d{ds}J_{ab}(2s+1)$ above, each meromorphic on $\mathbb C$. The derivative in $v$ is half the derivative in $s$ after substitution of $s=(v-1)/2$. Call the meromorphic extension in $v$ $\varphi$. Along a chain of continuation discs, $\tilde h'=\varphi$ on the first disc by the identity theorem, then on each next disc through the overlap. A pole of $\varphi$ inside a disc of the chain would be a pole of the holomorphic $\tilde h'$, so it is removable.
- At re-entry into $\mathsf V$, $\tilde h$ and $h$ are both holomorphic near the switch point (in $\mathcal V$, where $m$ is defined) with equal derivatives, so they differ by a constant. The germ is again $D^\kappa+m+C'$.

Induction over the pieces proves (b). Note that $m$ never changes on an excursion; only the constant does.

Section 7 explains the excursion by tracking a derivative. On the right of the strip the convergent series $D$ is still holomorphic. The correction to $D$ leaves as $h=m+C$, whose derivative $m'$ is meromorphic on the whole plane. If the germ continues, subtracting $D$ along the excursion continues $h$. Uniqueness of continuation fixes the derivative of that correction to $m'$, so on re-entry the correction differs from $h$ by a constant. This is the source of the $C$ allowed in Theorem 7.4(b).

### Part (c)

$B_x$ is the disc of Theorem 6.1. A point of $B_x\setminus L_x$ lies in $\Omega_\kappa$, so a germ of the family there can be written with this $\kappa$, and by (12) it is $\operatorname{Log}_\kappa(v-x)X_x+H+m+C$, where $H$, $m$ and $C$ are holomorphic on $B_x$.

The paper's closing sentence: every germ reached as in (a) or (b) at a point of $B_x\setminus L_x$ has the same coefficient $X_x$, so the coefficient of the logarithm at a candidate point does not change from branch to branch. The sentence is worded about reached germs, not about every germ of the family, because (b) covers $S$ only for paths from $\operatorname{Re}v>3$ and only at endpoints in $\mathcal V_\infty\setminus\mathcal X$. This is the analytic half of the proof. The arithmetic half (Theorem 3.1) said that coefficient is not identically zero at a dense set of points.


## Check your understanding

1. Why do the functions $M_x$ change no local coefficient?
2. For $G$, why is the constant $C$ always $0$?
3. What happens to an $S$-germ $D+M_2$ that loops once counterclockwise round $s=3$?

Answers. (1) They are holomorphic on all of $\mathcal V$, so adding one adds a holomorphic function near every candidate point, and the logarithm's coefficient is untouched. (2) Every path for $G$ stays in $\mathcal V_\infty$, where part (a) applies, and the starting germ is $D$ itself. (3) It becomes $D+M_2+4\pi^2$: the derivative of $M_2$ has a pole there with residue $-2\pi i$, and the loop adds $2\pi i\cdot(-2\pi i)$.

# 8. Section 8: the boundary for $G$ and $S$

## The section opener

The paper combines the two jobs: Theorem 3.1 gives points $x$ near any point of the line with $X_x'(x)\ne0$, so $X_x\not\equiv0$; by Theorem 7.4(c) every branch near such $x$ has non-trivial monodromy; a function meromorphic across the line would be single-valued there. The lemma is the local obstruction; the proof then steers an admissible germ to such a point without leaving the domain of the proposed extension.

## Lemma 8.1: the local obstruction

The paper proves: let $x\in\mathcal X\cap\mathcal V$ with $X_x'(x)\ne0$, $\kappa$ generic, $B_x$ the disc of Theorem 6.1. No germ $D^\kappa+m+C$ at a point $q$ of $B_x\setminus L_x$ agrees at $q$ with a function $f$ analytic on a punctured disc about $x$ containing $q$.

The steps.

1. Shrink to the smaller of $B_x$ and $f$'s disc; $q$ is in both.
2. The slit punctured disc (the disc minus the segment of $L_x$ in it) is connected and contains $q$. By Theorem 7.4(c), near $q$ the germ is $\operatorname{Log}_\kappa(v-x)X_x+H_1$ with $H_1$ holomorphic on the disc. Both this and $f$ are holomorphic on the slit punctured disc and agree near $q$, so by the identity theorem they agree on all of it.
3. Approach a point of the slit from its two sides. $f$ is analytic on the punctured disc, so continuous across the slit; so is $H_1$. $\operatorname{Log}_\kappa(v-x)$ jumps by $2\pi i$. So $2\pi iX_x(v)=0$ at every point of the slit.
4. $X_x$ vanishes on a segment, which has accumulation points, so $X_x\equiv0$ near $x$ by the identity theorem. That contradicts $X_x'(x)\ne0$.

Note that $f$ is only required to be analytic on a punctured disc: the lemma rules out even a function with an isolated singularity (pole or essential singularity) at $x$. A meromorphic function on a disc around the line is analytic off its poles, which are isolated; so around any candidate point, whether or not that point is itself a pole of the function, there is a punctured disc free of poles on which the function is analytic. The proof of Theorem 1.2 chooses its punctured disc that way and does not exclude a pole at the centre.

## Admissible germs of $S$ exist

This unnumbered paragraph comes just before the proof of Theorem 1.2.

The paper says: for $G$, continuation exists along every path in $\{\operatorname{Re}s>1\}\setminus\mathcal C_G$ starting in $\operatorname{Re}s>2$, by Theorem 7.4(a). For $S$, admissibility asks for a path along which continuation exists, so the statement for $S$ in Theorem 1.2 would be vacuous if there were none. Under $(\mathrm H_\infty)$, an admissible germ of $S$ exists at every point $s_1$ of $\{\operatorname{Re}s>0\}\setminus\mathcal C_S$, and by definition only there. In particular every disc $|s-iy|<r$ contains such a point, because its part in $\operatorname{Re}s>0$ is open and non-empty, and $\mathcal C_S$ is closed and discrete in $\operatorname{Re}s>0$ (Lemma 2.3).

The proof, step by step.

1. Take the path $\gamma(t)=s_1+t(1+i\kappa)$, $0\le t\le1$, with a slope $\kappa$ chosen below. Then $\operatorname{Re}\gamma(1)>1$ and $\operatorname{Re}\gamma(t)\ge\operatorname{Re}s_1>0$.
2. If $\operatorname{Re}s_1>\tfrac12$: $S$ is holomorphic along $\gamma$, which lies in $\operatorname{Re}s>\tfrac12$ and so misses $\mathcal C_S$. Its germ at $s_1$ is admissible.
3. Otherwise $0<\operatorname{Re}s_1\le\tfrac12$. Put $v_1=2s_1+1$, so $1<\operatorname{Re}v_1\le2$ and $v_1\notin\Pi$. Under $(\mathrm H_\infty)$, $\mathcal V_\infty=\mathcal V=\{1<\operatorname{Re}v<3\}$, so $v_1\in\mathcal V_\infty\setminus\mathcal X$.
4. Choose $\kappa$. Each $x\in\mathcal X$ lies on the eastward ray from $v_1$ for at most one slope, and $\mathcal X$ is countable, so all but countably many $\kappa$ put $v_1$ on no cut $L_x$. Fix such a $\kappa$.
5. The points $2\gamma(t)+1=v_1+2t(1+i\kappa)$ run east along the $\kappa$-line through $v_1$. Those with $\operatorname{Re}v\le\tfrac52$ lie in $\Omega_\kappa$: a cut through one of them would contain $v_1$.
6. By Theorem 5.3, $D^\kappa(2s+1)$ is holomorphic near each $\gamma(t)$ with $\operatorname{Re}(2\gamma(t)+1)\le\tfrac52$. It equals $S(s)$ wherever $2<\operatorname{Re}(2s+1)<3$, a strip no cut meets because $\operatorname{Re}x\le2$ on $\mathcal X$. The series $S$ itself is holomorphic near each $\gamma(t)$ with $\operatorname{Re}\gamma(t)>\tfrac12$. So the two descriptions agree on the overlap, where $\tfrac12<\operatorname{Re}\gamma(t)<1$, and continuing $S$ along $\gamma$ backwards from $\gamma(1)$ to $s_1$ is possible; it ends with the germ of $D^\kappa(2s+1)$ at $s_1$.
7. The path misses $\mathcal C_S$. Its points with $\operatorname{Re}(2s+1)\le2$ map into $\Omega_\kappa$, which contains no point of $\mathcal X$; its other points map to $\operatorname{Re}v>2$, which contains no point of $\Pi$. So the germ is admissible.

In the proof of Theorem 1.2 one needs admissible germs at base points inside the disc. This paragraph shows they exist near every point of the line, so the theorem is a statement about a non-empty family. The paper says the Lean form of this argument is described in Section 11; the declaration named there is `HInf.exists_admS_iff`, which takes only $(\mathrm H_\infty)$ and (Z1) to (Z3).

## The proof of Theorem 1.2

The paper treats $S$, noting the changes for $G$ ($v=s$; disc $|s-(1+iy)|<r$; Theorem 3.1 at $1+iy$ with $\varepsilon'$; $\alpha=x$ with $X_x'(x)=\Theta_G(x)$; strip and half-plane both $\operatorname{Re}s>1$; $\mathcal C_G$ for $\mathcal C_S$; $\operatorname{Re}x>1$ for $\operatorname{Re}\alpha>0$; Theorem 7.4(a) for (b)). Under $(\mathrm H_\infty)$, $\mathcal V_\infty=\mathcal V$ and $B<1$.

The steps for $S$:

1. Suppose $f$ is meromorphic on $\Delta=\{|s-iy|<r\}$ with germ $g$ at $s_1$ ($g$ admissible, $s_1\in\Delta$). Let $E$ be its pole set, discrete in $\Delta$.
2. Choose $0<\varepsilon'<r/2$. Apply Theorem 3.1 at $1+2iy$ with radius $2\varepsilon'$: there is $x=1+u$ with $|x-(1+2iy)|<2\varepsilon'$ and $\Theta_S(x)\ne0$. Put $\alpha=(x-1)/2=u/2$. Then $|\alpha-iy|=|u-2iy|/2<\varepsilon'$ and $\operatorname{Re}\alpha=\operatorname{Re}u/2>0$. Also $X_x'(x)=\tfrac12\Theta_S(x)\ne0$. (The point $1+2iy$ in $v$ corresponds to $iy$ in $s$; the factor $2$ in the radius is the same scaling.)
3. Check $x\in\mathcal X\cap\mathcal V$: $x=1+\rho/q$ has real part $1+\frac1{2q}$, in $(1,3)$, and above $2B_\infty=1$; it is a sum of two points of $\Sigma$.
4. Fix a generic $\kappa$ and the disc of Theorem 6.1 at $x$; in $s$ it is a disc $\Delta_\alpha$ about $\alpha$, shrunk to lie in $\Delta\cap\{0<\operatorname{Re}s<1\}$. (Shrinking keeps (12) true.)
5. Inside $\Delta_\alpha$ take a punctured disc about $\alpha$ free of $E$ and of $\mathcal C_S$ (both discrete; $\mathcal C_S$ is closed and discrete in $\operatorname{Re}s>0$ by Lemma 2.3), and a point $s_2$ in it off the cut.
6. Join $s_1$ to $s_2$ by a path in $(\Delta\cap\{\operatorname{Re}s>0\})\setminus(E\cup\mathcal C_S)$. Possible because $\Delta\cap\{\operatorname{Re}s>0\}$ is convex and removing a closed discrete set leaves it path connected. Along this path $g$ continues as $f$, since $f$ is holomorphic off $E$.
7. The germ of $f$ at $s_2$ is admissible: concatenate the path that made $g$ admissible with this one; it avoids $\mathcal C_S$, stays in $\operatorname{Re}s>0$, and continuation exists along it.
8. By Theorem 7.4(b) that germ is $D^\kappa+m+C$. But $f$ is analytic on the punctured disc about $\alpha$ containing $s_2$, contradicting Lemma 8.1.

What makes this work: the meromorphic $f$ would have to be analytic near $\alpha$ except perhaps at $\alpha$ itself, and the admissible germ, carried to a point near $\alpha$ inside $f$'s domain, is a branch with a logarithm there. The density of good points (Theorem 3.1) guarantees such an $\alpha$ inside every disc on the line.

## The paragraph before Theorem 8.2

The paper says the restriction that the path avoid the catalogue can be removed, both from the boundary statement (Theorem 8.2) and from the description of branches at endpoints off the catalogue (Corollary 8.3). The device: a path along which the function continues is replaced, piece by piece inside the discs of a continuation chain, by a path through the same holomorphic representatives avoiding the catalogue. In Theorem 8.2(a) the new endpoint can move to a nearby point inside the proposed extension disc. In Corollary 8.3 the endpoint is already off the catalogue, so the rebuilt path reaches the same germ there. Part (b) also avoids poles of the proposed extension. Theorem 10.1(a) uses RH to show that paths of continuation for $G$ avoid the entire catalogue. With only $(\mathrm H_\infty)$ the argument above leaves open whether a path meets a catalogue point: a point $x$ where $X_x\equiv0$ is not excluded, and a continuation might be holomorphic there and a path pass through it.

## Theorem 8.2: any path, and connected domains

The paper proves, under $(\mathrm H_\infty)$:

(a) If $\gamma$ is a continuous path in $\mathbb C$ starting in $\operatorname{Re}s>2$ along which $G$ continues analytically, then $\gamma$ stays in $\operatorname{Re}s>1$; and if $\gamma(1)$ lies in a disc centred on $\operatorname{Re}s=1$, the terminal germ $g$ does not extend meromorphically to that disc. The same for $S$ with start in $\operatorname{Re}s>1$, staying in $\operatorname{Re}s>0$, and discs centred on $\operatorname{Re}s=0$. The endpoint may be in the catalogue.

(b) Let $g$ be an admissible germ at $s_1$, of $G$ or of $S$. No connected open set containing $s_1$ and meeting the boundary line carries a meromorphic function with germ $g$ at $s_1$.

### Part (a), path inside the half-plane

The steps (for $G$).

1. A continuation chain: a partition $0=t_0<\dots<t_N=1$ and discs $U_j\subset\{\operatorname{Re}s>1\}$ with holomorphic $f_j$ on $U_j$, $\gamma([t_{j-1},t_j])\subset U_j$, and $f_j=f_{j+1}$ near $\gamma(t_j)$. The last gives the germ $g$ at $\gamma(1)$.
2. Junctions: small discs $U_j'\subset U_j\cap U_{j+1}$ about $\gamma(t_j)$ where $f_j=f_{j+1}$, and points $q_j\in U_j'\setminus\mathcal C_G$. Keep $q_0=\gamma(0)$, off $\mathcal C_G$ since $\operatorname{Re}q_0>2$. Choose $q_N=s_2$ off $\mathcal C_G$, close to $\gamma(1)$, inside $U_N$, inside the boundary disc, and inside the neighbourhood where a proposed extension agrees with $g$.
3. Join $q_{j-1}$ to $q_j$ inside $U_j\setminus\mathcal C_G$. A disc minus a relatively closed discrete set is path connected: take a polygonal path, which is compact, so it meets finitely many removed points, and detour round each.
4. Follow $f_j$ on the $j$-th piece. At $q_j$ the representatives agree, so the concatenation is a continuation ending with the germ of $f_N$ at $s_2$. The path avoids $\mathcal C_G$ and stays in $\operatorname{Re}s>1$, so this germ is admissible.
5. A meromorphic extension of $g$ to the boundary disc would agree with $f_N$ near $s_2$, so it would extend an admissible germ, contradicting Theorem 1.2.

### Part (a), path leaving the half-plane

Let $t^*$ be the first time with $\operatorname{Re}\gamma(t^*)=1$. Since continuation exists at $\gamma(t^*)$, the germ there is holomorphic on some disc about $\gamma(t^*)$, a disc centred on the line. For $t<t^*$ close to $t^*$, $\gamma(t)$ is in that disc and the germ at $\gamma(t)$ extends to it (as a holomorphic, hence meromorphic, function). But $\gamma$ up to $t$ stays in $\operatorname{Re}s>1$, and the first part forbids such an extension. So no such $t^*$ exists, and by continuity $\gamma$ never leaves the half-plane.

For $S$: $\gamma(0)$ has $\operatorname{Re}s>1$, off $\mathcal C_S$, which lies in $\operatorname{Re}s\le\tfrac12$ (since $\Pi$ has real parts at most $2$, $2s+1\in\Pi$ gives $\operatorname{Re}s\le\tfrac12$).

### Part (b)

Let $f$ be meromorphic on a connected open $W$ containing $s_1$ and meeting the line.

1. Take a path in $W$ from $s_1$ to the line; let $t^*$ be its first contact, at $s_0$. Before $t^*$ the path is in the open half-plane.
2. Take a disc $B_0$ about $s_0$ with closure in $W$, and $t<t^*$ with $\gamma(t)\in B_0$.
3. Pick $q$ in a small disc about $\gamma(t)$ inside $B_0$ and the half-plane, off the poles of $f$ and off the catalogue; append a segment from $\gamma(t)$ to $q$.
4. The compact path from $s_1$ to $q$ lies in the open half-plane intersected with $W$. Cover it by finitely many discs there and perturb it inside their union to avoid the poles of $f$ and the catalogue, keeping $s_1$ fixed and the end in $B_0$. Since $f$ is single-valued on $W$, following $f$ along the new path gives $f$'s germ at the end, with no homotopy argument needed.
5. That terminal germ is admissible and extends meromorphically to $B_0$ as $f$; $B_0$ is a disc centred on the line containing the endpoint. Contradiction with Theorem 1.2.

The perturbation stops strictly before the path touches the line.

What (b) adds: a natural boundary is often stated for discs; (b) says no connected open set reaching the line can carry an extension, however it is shaped.

## Corollary 8.3

The paper proves: under $(\mathrm H_\infty)$, if $\gamma$ starts in $\operatorname{Re}s>2$, $G$ continues along it, and $\gamma(1)\notin\mathcal C_G$, the terminal germ is admissible; likewise for $S$ from $\operatorname{Re}s>1$ with $\gamma(1)\notin\mathcal C_S$.

Proof: Theorem 8.2(a) keeps $\gamma$ in the half-plane; then the chain construction with $q_N=\gamma(1)$ (allowed, since it is off the catalogue) gives a path avoiding the catalogue with the same terminal germ.

The paper's closing sentence: by Theorem 7.4, every germ reached along any path and ending off the catalogue is $D^\kappa+m$ for $G$, and $D^\kappa+m+C$ for $S$ at endpoints with $0<\operatorname{Re}s<1$; near a candidate point it has the coefficient $X_x$.

## Check your understanding

1. Why does Lemma 8.1 allow $f$ an isolated singularity at $x$?
2. In the proof of Theorem 1.2, why must $\Delta_\alpha$ lie inside $\{0<\operatorname{Re}s<1\}$?
3. Why can Theorem 8.2(a) allow the endpoint to be in the catalogue?

Answers. (1) The argument only uses $f$ on the slit punctured disc and its continuity across the slit; the point $x$ itself plays no role. (2) Theorem 7.4(b) describes germs at points of $\mathcal V_\infty\setminus\mathcal X$. Under $(\mathrm H_\infty)$, for $S$ this is the strip $1<\operatorname{Re}v<3$ with the candidate points removed, or $0<\operatorname{Re}s<1$ with the catalogue $\mathcal C_S$ removed. (3) The proof moves the endpoint to a nearby $s_2$ off the catalogue, inside the same disc and inside the neighbourhood where the proposed extension agrees with the germ.

# 9. Section 9: two more kernels

## The section opener

The paper says Sections 5 to 8 used three things about $G$ and $S$: the kernel facts (K1) to (K3), the local calculation at a pinch of two logarithms (Theorem 6.1), and the non-vanishing of the derivative $X_x'(x)$ at dense points, which Section 3 supplies. This section proves Theorem 1.3. Each of its two series changes one of these layers and leaves the rest of the argument as it stands, so the section shows which parts of the method depend on what. The constructions before the proofs of Theorem 1.3 work without $(\mathrm H_\infty)$. Lemma 9.3 and Theorem 9.4 need $B<1$. In the boundary proofs $(\mathrm H_\infty)$ puts the dense nonzero points into the continuation region.

For $G_2$ the kernel is different, but Proposition 9.1 shows that it has the properties Sections 5 to 8 use, on a half-plane, as for $G$. So the change is in the arithmetic: $X_x'(x)$ becomes $\tfrac12\sum c(a)c(b)\mathrm B(a/2,b/2)$, and the argument of Section 3 has to be run again for this sum, with a new main term and a new far-pair bound.

For $G_{\log}$ the local calculation changes. The weight $\log q$ turns one copy of $P$ into $Q=-P'$, which has poles where $P$ has logarithms. At a pinch a logarithm now meets a pole, and Lemma 6.2 takes the place of the calculation with two logarithms. The coefficient of the logarithm is then a value of the kernel, not an integral of it, and its value at the point is $-\Theta_G(x)$. Theorem 3.1 finds a dense family with $\Theta_G(x)\ne0$ under $B<1$, and $(\mathrm H_\infty)$ places this family in $\mathcal X$. So no new arithmetic is needed.

A way to hold the section in mind: there are three layers (kernel facts, pinch calculation, arithmetic). $G_2$ keeps the pinch calculation, supplies the kernel facts afresh, and redoes the arithmetic. $G_{\log}$ redoes the pinch calculation and keeps the arithmetic.

## Section 9.1: the squares

The paper puts $v=2s$ and $D(v)=G_2(v/2)=\sum_{p,q}(p^2+q^2)^{-v/2}$, absolutely convergent for $\operatorname{Re}v>2$, and says that in this subsection $\mathcal K$, $D$, $J_{ab}$, $X_x$ and $D^\kappa$ are the objects of (5), (6) and (11) for the kernel of the next proposition.

So the letters are reused with a new kernel. $\Sigma$, $\Pi$, $\mathcal X$, $c(a)$, the cuts and the separating graphs do not involve the kernel and are the same sets as before.

### Proposition 9.1: the kernel of $G_2$

The paper proves: with $\mathcal V=\{\operatorname{Re}v>1\}$ and
$$\mathcal K(z,v)=\frac{\Gamma(z/2)\,\Gamma((v-z)/2)}{2\,\Gamma(v/2)},$$
(K1) and (K2) hold, and for $2<\operatorname{Re}v<3$ and $1<c<\operatorname{Re}v-1$,
$$D(v)=\frac1{2\pi i}\int_{(c)}\mathcal K(z,v)P(z)P(v-z)\,dz.$$

The steps.

- (K1). $\Gamma(z/2)$ is holomorphic for $\operatorname{Re}z>0$, $\Gamma((v-z)/2)$ for $\operatorname{Re}z<\operatorname{Re}v$, and $1/\Gamma$ is entire.
- (K2). Write $t=\operatorname{Im}z$. (Z6) applied to $\Gamma(z/2)$, whose imaginary part is $t/2$, gives a factor $e^{-\pi|t|/4}$. Applied to $\Gamma((v-z)/2)$, whose imaginary part is $(\operatorname{Im}v-t)/2$, it gives $e^{-\pi|\operatorname{Im}v-t|/4}$, which for $v$ in a compact set is at most a constant times $e^{-\pi|t|/4}$. The product decays like $e^{-\pi|t|/2}$ times a power of $1+|t|$, and $1/\Gamma(v/2)$ is bounded on the compact set. The paper notes this is the rate of $S$, half that of $G$.
- The integral. Write $(p^2+q^2)^{-s}=q^{-2s}(1+(p/q)^2)^{-s}$ and use the Mellin–Barnes formula with $x=(p/q)^2$: $(1+x)^{-s}=\frac1{2\pi i}\int_{(d)}K_s(w)x^{-w}\,dw$ for $0<d<\operatorname{Re}s$. Since $x^{-w}=p^{-2w}q^{2w}$, the integrand is $K_s(w)\,p^{-2w}q^{-2s+2w}$. Substitute $z=2w$, $dw=\tfrac12dz$, and $v=2s$: the powers become $p^{-z}q^{-(v-z)}$ and the kernel becomes $\tfrac12K_{v/2}(z/2)=\mathcal K(z,v)$. The factor $\tfrac12$ comes from $dw$, as it did for $S$. The line $\operatorname{Re}w=d$ becomes $\operatorname{Re}z=c=2d$.
- Fubini. On $\operatorname{Re}z=c$ with $1<c<\operatorname{Re}v-1$ the prime sums are bounded by $P(c)P(\operatorname{Re}v-c)<\infty$. Times the integrable bound (K2), this is a majorant, as in Section 2.3.

The paper then adds that the proof gives the formula for every $\operatorname{Re}v>2$, and that the proposition states it on the strip $2<\operatorname{Re}v<3$ because that is what the formal proof records.

### The paragraph after Proposition 9.1: Sections 5 to 8 apply

The paper says the proposition puts $G_2$ in the setting of Sections 5 to 8. Those sections use nothing about the kernel beyond (K1) to (K3), and the domain $\mathcal V$ is a half-plane, as for $G$, not a strip, as for $S$. The excursion argument of Theorem 7.4(b), which produced the constant $C$ for $S$, was needed only because a path for $S$ can leave its strip; a path in $\operatorname{Re}v>2B_\infty$ never leaves this $\mathcal V$. So Theorems 5.3, 6.1, 7.3, 7.4(a),(c) and Lemma 8.1 hold for this $D$, with $C=0$: $D$ continues along every path in $\{\operatorname{Re}v>2B_\infty\}\setminus\Pi$ starting in $\operatorname{Re}v>2$, every germ reached that way is $D^\kappa+m$ with $m\in\mathcal M$, and near $x\in\mathcal X$ every such germ is $\operatorname{Log}_\kappa(v-x)X_x(v)$ plus a holomorphic function. The candidate points in the variable $v$ are the points of $\mathcal X$, as for $G$; in the variable $s$ they are the points $x/2$, and under $(\mathrm H_\infty)$, where $2B_\infty=1$, they form the catalogue $\mathcal C_2$ of Theorem 1.3.

One step in this paragraph closes the gap between the strip and the half-plane. Theorem 5.3's last claim is $D^\kappa=D$ on $\Omega_\kappa\cap\{\operatorname{Re}v>2\}$, and its proof uses (K3) at every such $v$, while the proposition gives (K3) only for $2<\operatorname{Re}v<3$. The paper's argument: on the strip the last step of that proof gives $D^\kappa=D$; both sides are holomorphic on $\Omega_\kappa\cap\{\operatorname{Re}v>2\}$, which is the whole half-plane $\operatorname{Re}v>2$, because no cut $L_x$ reaches it ($\operatorname{Re}x\le2$ on $\mathcal X$, and $L_x$ runs west from $x$); so $D^\kappa=D$ on all of it by the identity theorem.

To check the claim "nothing beyond (K1) to (K3)" for yourself, go through Sections 5 to 8 and mark each use of the kernel. The uses are: holomorphy of $\mathcal K$ on $0<\operatorname{Re}z<\operatorname{Re}v$ (for the integrand, for $J_{ab}$, and for $f(t,\mu)$ in Theorem 6.1); the decay bound on the tails; and the identification with the series for $\operatorname{Re}v>2$. The one place a specific kernel appears is Theorem 7.4(b), for $S$, which is not needed here.

### Lemma 9.2: the coefficient for $G_2$

The paper proves: for $x\in\mathcal X\cap\mathcal V$, with the derivative taken in $v$,
$$X_x'(x)=\tfrac12\Theta_2(x),\qquad\Theta_2(x)=\sum_{a+b=x}c(a)c(b)\,\mathrm B\bigl(\tfrac a2,\tfrac b2\bigr).$$
At $x=1+u$ with $u\ne1$ the pairs $(1,u)$ and $(u,1)$ contribute $-2c(u)\mathrm B(\tfrac12,\tfrac u2)$ to $\Theta_2(x)$, and $\mathrm B(\tfrac12,\tfrac u2)\ne0$ for non-real $u$.

The steps. As for (7), $\partial_vJ_{ab}(a+b)=\mathcal K(a,a+b)$, and here $\mathcal K(a,a+b)=\Gamma(a/2)\Gamma(b/2)/(2\Gamma((a+b)/2))=\tfrac12\mathrm B(a/2,b/2)$. The main pairs give $c(1)c(u)\{\mathrm B(\tfrac12,\tfrac u2)+\mathrm B(\tfrac u2,\tfrac12)\}=-2c(u)\mathrm B(\tfrac12,\tfrac u2)$, using $c(1)=-1$ and the symmetry of the Beta function. For the non-vanishing, $\mathrm B(\tfrac12,\tfrac u2)=\Gamma(\tfrac12)\Gamma(\tfrac u2)/\Gamma(\tfrac{1+u}2)$. $\Gamma$ has no zeros, so the numerator is not zero; and for non-real $u$ neither $u/2$ nor $(1+u)/2$ is a pole of $\Gamma$, whose poles are real, so the quotient is finite and non-zero.

The paper adds two remarks. In the variable $s=v/2$ the derivative of $X_x(2s)$ at $x/2$ is $\Theta_2(x)$ itself: the factor $\tfrac12$ cancels against $dv/ds=2$, as for $S$. And where $S$ needed the cotangent argument of Lemma 2.4 to show that its main-term bracket does not vanish, here it is immediate, because the main term is a single Beta value.

At $x=2$ the only pair is $(1,1)$, as in the sign check of Section 6, so $\Theta_2(2)=\mathrm B(\tfrac12,\tfrac12)=\Gamma(\tfrac12)^2=\pi$. This is the case $u=1$ that the two-pair formula excludes: the diagonal pair occurs once, and the value is $\pi$, not $2\pi$.

### Lemma 9.3: far pairs for $G_2$

The paper proves: assume $B<1$ and let $Y>0$. There is $H_0\ge2Y+2$ such that for all $u$ with $0<\operatorname{Re}u\le1$, $|\operatorname{Im}u|\le Y$, and all $H\ge H_0$,
$$\sum_{\substack{a+b=1+u,\ a,b\ne1\\|\operatorname{Im}a|>H}}\bigl|c(a)c(b)\mathrm B\bigl(\tfrac a2,\tfrac b2\bigr)\bigr|\le2e^{-H}.$$

The steps follow Lemma 3.4. The extra pairs have $\operatorname{Re}a,\operatorname{Re}b\in[1-B,B]$, so $a/2$ and $b/2$ have real parts in $[\tfrac{1-B}2,\tfrac B2]$, a compact subinterval of $(0,1)$, where (Z6) applies. With $t=\operatorname{Im}a$: $|\operatorname{Im}b|\ge|t|-Y$, $|c(a)c(b)|\ll\log^2(|t|+Y+3)$, and $O(\log(j+4))$ points $a$ have $|\operatorname{Im}a|\in[j,j+1]$. (Z6), with imaginary parts $t/2$ and $\operatorname{Im}b/2$, gives
$$|\Gamma(a/2)\Gamma(b/2)|\ll(1+|t|+Y)^2e^{-\pi(2|t|-Y)/4}.$$
For the denominator, $(1+u)/2$ has real part in $[\tfrac12,1]$ and bounded imaginary part, a compact set on which $1/\Gamma$ is bounded. So each term is $\ll(1+|t|)^4e^{-\pi|t|/2}$, the rate of $S$, and summing over $|t|>H$ gives $\ll(H+3)^5e^{-\pi H/2}\le2e^{-H}$ for large $H$.

The paper then notes that only finitely many pairs at $1+u$ have $|\operatorname{Im}a|\le H$: the two main pairs, and pairs with $a,b\ne1$, for which $a$ is $1/k$ or $\rho/n$ with $n\le\lfloor1/(1-B)\rfloor$ and $|\operatorname{Im}\rho|\le nH$. So $\Theta_2(1+u)$ converges absolutely. The main term of Lemma 9.2 and this far-pair bound are the two inputs the counting argument of Section 3 needs.

### Theorem 9.4: dense points for $\Theta_2$

The paper proves: assume $B<1$. For $y\in\mathbb R$ and $\varepsilon>0$, the disc $|x-(1+iy)|<\varepsilon$ contains infinitely many points $x=1+\rho/q$, with $\rho$ a zero on the critical line and $q$ prime, at which $\Theta_2(x)\ne0$. The paper adds that the points need not be those of Theorem 3.1: the two families are found separately.

The proof is the proof of Theorem 3.1 with $\Theta_2$ in place of $\Theta_G$. What carries over unchanged, and why:

- The reduction to $y>0$ and $0<\varepsilon<\min(y,1)$. It used $c(\bar a)=c(a)$ and the conjugation symmetry of the kernel values; here $\overline{\mathrm B(\bar a/2,\bar b/2)}=\mathrm B(a/2,b/2)$.
- Good pairs and near-bad pairs. They are defined by the points alone (the representations of $\rho/q$; the existence of a low extra pair), with no kernel involved. So Theorem 3.3 and the count $\ll(\log X\log\log X)^2$ of near-bad pairs apply as they are.

What is new:

- The main term. By Lemma 9.2 it is $-2c(u)\mathrm B(\tfrac12,\tfrac u2)$. The function $\mathrm B(\tfrac12,\tfrac u2)$ is continuous and non-zero on the closed disc $|u-iy|\le\varepsilon$, which misses the real axis, so its modulus there is at least some $\lambda>0$. With $|c(u)|\ge1/q$ and $q\ll X$ the main term is $\gg1/X$.
- The far pairs. Lemma 9.3 with $H=2\log X$ bounds them by $2X^{-2}$.

For large $X$ the main term exceeds the far-pair total, and the count of surviving points is as before.

### Proof of Theorem 1.3(a) and (b) for $G_2$

The paper assumes $(\mathrm H_\infty)$, so $2B_\infty=1$ and $B<1$, and translates between $s$ and $v=2s$. A point $s$ with $\operatorname{Re}s>\tfrac12$ lies in $\mathcal C_2$ exactly when $2s\in\Pi$, so $s\mapsto2s$ carries paths in $\{\operatorname{Re}s>\tfrac12\}\setminus\mathcal C_2$ starting in $\operatorname{Re}s>1$ to paths in $\{\operatorname{Re}v>1\}\setminus\Pi$ starting in $\operatorname{Re}v>2$, and $G_2(s)=D(2s)$. An admissible germ $g$ of $G_2$ at $s_1$ becomes a germ $g(v/2)$ of $D$ at $2s_1$ that is admissible in the sense used for $G$ in Theorem 1.2.

Part (a), continuation. This is Theorem 7.4(a) for this $D$.

Part (a), where admissible germs exist. An admissible germ sits at the end of a path in $\{\operatorname{Re}s>\tfrac12\}\setminus\mathcal C_2$, so only points of that set carry one. Conversely take such an $s_1$ and put $v_1=2s_1$, so $\operatorname{Re}v_1>1$ and $v_1\notin\Pi$. As in the argument for $S$ in Section 8, all but countably many slopes $\kappa$ put $v_1$ on no cut $L_x$; fix one. The segment $v_1+t(1+i\kappa)$, $0\le t\le2$, has real parts at least $\operatorname{Re}v_1>1$, ends at real part $\operatorname{Re}v_1+2$, which is above $2$, and meets no point $x\in\Pi$ with $\operatorname{Re}x>1$, since such an $x$ on it would put $v_1$ on $L_x$. Continue $D$ along it from its east end back to $v_1$, which Theorem 7.4(a) allows. The result is an admissible germ at $v_1$, hence one of $G_2$ at $s_1$. Since $\mathcal C_2$ is closed and discrete in $\operatorname{Re}s>\tfrac12$ (Lemma 2.3), every disc $|s-(\tfrac12+iy)|<r$ contains such points.

Part (b). Let $g$ be admissible at $s_1$ with $|s_1-(\tfrac12+iy)|<r$, and suppose $f$ is meromorphic on that disc with germ $g$ at $s_1$. Then $f(v/2)$ is meromorphic on $|v-(1+2iy)|<2r$ and extends the admissible germ $g(v/2)$ at $2s_1$. Now run the proof of Theorem 1.2 for $G$, with $D$ in place of $G$ and this disc. The one change is the source of the point $x$: choose $0<\varepsilon'<r$ and apply Theorem 9.4 at $1+2iy$ with $\varepsilon'$. It gives $x\in\mathcal X$ with $\operatorname{Re}x>1$, $|x-(1+2iy)|<\varepsilon'$ and, by Lemma 9.2, $X_x'(x)=\tfrac12\Theta_2(x)\ne0$. Theorem 7.4(a) and Lemma 8.1, which hold for this $D$, give the contradiction as before.

The doubling to keep straight: the line $\operatorname{Re}s=\tfrac12$ is the line $\operatorname{Re}v=1$, the point $\tfrac12+iy$ is $1+2iy$, and a disc of radius $r$ in $s$ is a disc of radius $2r$ in $v$.

## Section 9.2: one logarithm

The paper says $G_{\log}$ sits between $G$ and $T$: one of its two factors is $P$, the other is $Q$. It mentions a related series in the literature. Matsumoto, Nawashiro and Tsumura continue the double series $\sum_{m_1,m_2\ge1}\Lambda(m_2)m_1^{-s_1}(m_1+m_2)^{-s_2}$ meromorphically to $\mathbb C^2$. That series also carries a weight on one variable only, the von Mangoldt function, but its other variable runs over all positive integers with coefficient $1$; in $G_{\log}$ the weight $\log q$ is on one prime and both variables run over primes.

### Lemma 9.5: the integral for $G_{\log}$

The paper proves: for $\operatorname{Re}s>2$ and $1<c<\operatorname{Re}s-1$,
$$G_{\log}(s)=\frac1{2\pi i}\int_{(c)}K_s(z)P(z)Q(s-z)\,dz.$$

The steps, as for (4). The Mellin–Barnes integrand for $(p+q)^{-s}$ is $K_s(z)p^{-z}q^{-(s-z)}$. Multiply by $\log q$ and sum over both primes: $\sum_pp^{-z}=P(z)$ and $\sum_q\log q\,q^{-(s-z)}=Q(s-z)$. The majorant on the line is $P(c)Q(\operatorname{Re}s-c)$ times the bound for $K_s$, finite because $c>1$ and $\operatorname{Re}s-c>1$.

### Why the same contours serve

In this subsection $v=s$, $\mathcal V=\{\operatorname{Re}s>1\}$, $\mathcal V_\infty=\{\operatorname{Re}s>2B_\infty\}$, and $\mathcal X$, $L_x$, $\Omega_\kappa$ are as for $G$. The paper explains why the sheet can be built with the contours of Section 5. The left factor $P^\kappa(z)$ has a cut west of every left point $a$, so the contour must pass east of each $a$, as before. The right factor $Q(s-z)$ is single-valued, with poles at the right points $s-b$. A contour could pass a pole on either side, but the two choices differ by a residue, which contains the value $P^\kappa(s-b)$ and so is itself multivalued; to define one function the paper keeps every right point east of the contour, as in Section 5. The condition for such a contour to exist is then the same as before: on a $\kappa$-line holding a left point $a$ and a right point $s-b$, the right point must be east of the left one. So separating graphs, Lemma 5.2 and the cuts $L_x$ carry over unchanged, and a cut $L_x$ is now where a pole of the right factor meets the cut of a logarithm of the left factor.

The point about the residue, spelled out. Moving the contour from one side of the pole at $z=s-b$ to the other changes the integral by the residue there, which is $R_b$ times the rest of the integrand at the pole, $K_s(s-b)P^\kappa(s-b)$, up to sign. The factor $P^\kappa(s-b)$ is a function of $s$ with its own cuts. So the side on which each pole is passed is a real choice, and the paper makes it once, in the way that gives the series for $\operatorname{Re}s>2$.

### Theorem 9.6: sheets for $G_{\log}$

The paper proves: for $s\in\Omega_\kappa$ let
$$D^\kappa_{\log}(s)=\frac1{2\pi i}\int_\Gamma K_s(z)\,P^\kappa(z)\,Q(s-z)\,dz,$$
with $\Gamma$ any separating $\kappa$-graph for $s$. The value does not depend on $\Gamma$; $D^\kappa_{\log}$ is holomorphic on $\Omega_\kappa$; and $D^\kappa_{\log}=G_{\log}$ on $\Omega_\kappa\cap\{\operatorname{Re}s>2\}$.

The proof follows Theorem 5.3, with these substitutions. On a separating graph, $z$ lies on no cut $\ell_a$, and $s-z$ is not a pole of $Q$, because every right point is strictly east of the graph; so the integrand is holomorphic near $\Gamma$, and the homotopy of separating graphs stays in the set where it is holomorphic. On the vertical tails both $\operatorname{Re}z$ and $\operatorname{Re}(s-z)$ are at least $B_\infty+2\eta$, so Lemma 5.1(b) bounds $P^\kappa(z)$ and Lemma 2.2 bounds $Q(s-z)$ by $\ll\log|\operatorname{Im}z|$; with the decay of $K_s$ this dominates the integrand, locally uniformly in $s$. For $\operatorname{Re}s>2$ the line $\operatorname{Re}z=c$ with $1<c<\operatorname{Re}s-1$ separates, $P^\kappa=P$ on it, and the integral is that of Lemma 9.5.

### Theorem 9.7: the local model for $G_{\log}$

The paper proves: let $x\in\mathcal X\cap\mathcal V$ and let $\kappa$ be generic. Put
$$Y_x(s)=-\sum_{a+b=x}c(a)c(b)\,K_s(s-b)=-\sum_{a+b=x}c(a)c(b)\,\frac{\Gamma(s-b)\Gamma(b)}{\Gamma(s)}.$$
Then $Y_x$ is holomorphic on $\operatorname{Re}s>1$, and there is $r>0$ such that the disc $|s-x|<r$ minus $L_x$ lies in $\Omega_\kappa$, and on it
$$D^\kappa_{\log}(s)=\operatorname{Log}_\kappa(s-x)\,Y_x(s)+H(s),$$
with $H$ holomorphic on the whole disc.

Holomorphy of $Y_x$. The sum is finite (Lemma 2.3). Each $b\in\Sigma$ has $0<\operatorname{Re}b\le1$, so for $\operatorname{Re}s>1$ the argument $s-b$ has positive real part and $\Gamma(s-b)$ is holomorphic; $1/\Gamma(s)$ is entire.

The local form, step by step.

1. Geometry. The configuration at $s=x$, the outer contour $\Gamma_{\mathrm{out}}$, the radius $r$ and the arcs depend only on the positions of the left and right points, which are those of $G$. So they are chosen as in Theorem 6.1, with the same four conditions on $r_0$. The fourth is now applied to the kernel in the pole–logarithm calculation (step 3). The right points in Figure 1 are pole candidates, so omit their eastward rays when using that figure here. In the bound that makes $I_{\mathrm{out}}$ holomorphic, the right factor is bounded on the tails by Lemma 2.2 in place of Lemma 5.1(b).
2. The two factors on an arc. Fix a collision $(a,b)$, and put $t=(z-a)/e$, $\delta=s-x$, $\epsilon=\delta/e$. The left factor is $P^\kappa(z)=c(a)\operatorname{Log}t+E_1(t)$, as before. For the right factor, $Q$ has residue $R_b=-c(b)$ at $b$, and its argument is $s-z=b+e(\epsilon-t)$ (from $s=x+\delta$, $z=a+et$ and $x=a+b$). So
$$Q(s-z)=\frac{-c(b)\,e^{-1}}{\epsilon-t}+E_2(\epsilon-t),$$
with $E_2$ holomorphic.
3. The kernel. Put $f(t,\mu)=e\,K_{x+e\mu}(a+et)$, so that $f(t,\epsilon)\,dt=K_s(z)\,dz$. The fourth condition on $r_0$ is that $f$ be holomorphic for $|t|<2r_0$, $|\mu|<2r_0$. That is possible because $\operatorname{Re}a>0$ and $\operatorname{Re}(x-a)=\operatorname{Re}b>0$: the two Gamma arguments, $a+et$ and $b+e(\mu-t)$, keep positive real part for small $t$ and $\mu$.
4. Apply Lemma 6.2 with $c_1=c(a)$ and $c_2=-c(b)e^{-1}$. The arc integral is $-c(a)c(b)e^{-1}f(\epsilon,\epsilon)\operatorname{Log}\epsilon$ plus a function holomorphic in $\epsilon$, on the disc of the radius the lemma provides; $r$ is shrunk so that $|\epsilon|$ stays below that radius for every collision.
5. Translate back. $e^{-1}f(\epsilon,\epsilon)=K_s(a+\delta)=K_s(s-b)$, since $a+\delta=x-b+\delta=s-b$; and $\operatorname{Log}\epsilon=\operatorname{Log}_\kappa\delta-i\theta$, the second piece going into the holomorphic part.
6. Sum over the collisions, each ordered pair once.

The paper then contrasts the two local models. For $G$ the arc gave $c(a)c(b)\operatorname{Log}_\kappa(v-x)J_{ab}(v)$, whose coefficient is an integral from $a$ to $v-b$ that vanishes at $v=x$: there the sheet behaves like $(v-x)\log(v-x)$. Here the coefficient is the kernel evaluated at the pole, and $D^\kappa_{\log}$ behaves like a multiple of $\log(s-x)$ itself, with a coefficient that need not vanish at $x$. So when $Y_x(x)\ne0$ a branch of $G_{\log}$ is unbounded near $x$, while a branch of $G$ stays bounded near its candidate points. ("Behaves like $(v-x)\log(v-x)$" describes the non-holomorphic part of the sheet of $G$ when $X_x'(x)\ne0$; the three cases are set out under Theorem 6.1 above.)

The sign check in Section 9.2 starts from $A(X)=\sum_{p+q\le X}\log q=\sum_{p\le X}\vartheta(X-p)$, where $\vartheta(y)=\sum_{q\le y}\log q$. The prime number theorem gives $\vartheta(y)=y+o(y)$. For any chosen relative error, choose a fixed cutoff above which this error bound holds. Below that cutoff the total error is $O(\pi(X))$, where $\pi(t)$ counts primes up to $t$. Thus $A(X)$ is asymptotic to $\sum_{p\le X}(X-p)=\int_2^X\pi(t)\,dt\sim X^2/(2\log X)$. Partial summation then writes $G_{\log}(2+\delta)$ as $(2+\delta)\int_4^\infty A(t)t^{-3-\delta}\,dt$. The substitution $t=e^y$ leads to $\int_{\log4}^\infty e^{-\delta y}\,dy/y$, which grows like $-\log\delta$ as $\delta\to0^+$. This agrees with $Y_2(2)=-1$ in the local model when $B_\infty<1$. The paper uses the calculation to check the sign and normalization.

### Theorem 9.8: rotation and every branch for $G_{\log}$

The paper notes that the rotation argument uses only that the jump functions are holomorphic on the whole domain, and $Y_x$ is. It lets $\mathcal M_{\log}$ be the set of finite integer combinations of the functions $2\pi iY_x$, $x\in\mathcal X$, all holomorphic on $\operatorname{Re}s>1$, and proves:

(a) If $s_1\in\Omega_\kappa\cap\Omega_{\kappa'}$ with $\kappa<\kappa'$, then as germs at $s_1$, $D^{\kappa'}_{\log}-D^\kappa_{\log}=\sum_x2\pi iY_x$, the finite sum over $x\in\mathcal X$ in the open eastward sector at $s_1$ between the two directions.

(b) A germ $D^\kappa_{\log}+m$, $m\in\mathcal M_{\log}$, continues along every path in $\mathcal V_\infty\setminus\mathcal X$ and stays in this family. In particular $G_{\log}$ continues along every path in $\{\operatorname{Re}s>2B_\infty\}\setminus\Pi$ starting in $\operatorname{Re}s>2$, and each germ reached is $D^\kappa_{\log}+m$.

(c) For $x\in\mathcal X\cap\mathcal V$ and generic $\kappa$ there is a disc $B_x$ about $x$ such that every germ of this family at a point of $B_x\setminus L_x$ is $\operatorname{Log}_\kappa(s-x)Y_x$ plus a function holomorphic on $B_x$.

The proof is Section 7 again. Lemma 7.1 holds as stated, with the same proof, since every sheet equals $G_{\log}$ on $\operatorname{Re}s>2$ (Theorem 9.6). In the proof of Lemma 7.2, Theorem 9.7 replaces Theorem 6.1: at each point $x_j$ on the ray the two logarithms differ by $2\pi i$ on the west sector, so the jump there is $2\pi iY_{x_j}$, and the induction needs only that the earlier jumps are holomorphic on $\mathcal V$. The proof of Theorem 7.3 then gives (a), and (b), (c) follow from (a) and Theorem 9.7 as Theorem 7.4(a),(c) followed from Theorems 7.3 and 6.1. The paths in part (b) lie in $\mathcal V_\infty\subseteq\mathcal V$, so there are no excursions outside $\mathcal V$ and no constant.

So this is the $G$ case of Section 7, not the $S$ case: a half-plane, and no constant $C$.

### Lemma 9.9: the value of the coefficient

The paper proves: for $x\in\mathcal X$, $Y_x(x)=-\Theta_G(x)$; and at $x=1+u$ with $u\ne1$ the pairs $(1,u)$ and $(u,1)$ contribute $2c(u)/u$ to $Y_x(x)$. (At $u=1$ the single pair $(1,1)$ gives $Y_2(2)=-1$.)

The steps. For a pair $(a,b)$ at $x$, $x-b=a$, so $K_x(x-b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)=\mathrm B(a,b)$, and $Y_x(x)=-\sum c(a)c(b)\mathrm B(a,b)=-\Theta_G(x)$. For the main pairs, $\mathrm B(1,u)+\mathrm B(u,1)=2\Gamma(u)/\Gamma(1+u)=2/u$ and $c(1)=-1$, so they contribute $-c(1)c(u)\cdot\tfrac2u=2c(u)/u$.

On the sign: this is the negative of the main term $-2c(u)/u$ of $\Theta_G$ in Section 3, as $Y_x(x)=-\Theta_G(x)$ requires. Theorem 3.1 under $B<1$ gives infinitely many $x$ with $\Theta_G(x)\ne0$ near every point of the line. Under $(\mathrm H_\infty)$ these points lie in $\mathcal X$, so Lemma 9.9 gives $Y_x(x)\ne0$ there.

### Lemma 9.10: the obstruction for $G_{\log}$

The paper proves: let $x\in\mathcal X\cap\mathcal V$ with $Y_x(x)\ne0$, $\kappa$ generic, and $B_x$ be the disc of Theorem 9.8(c). No germ $D^{\kappa}_{\log}+m$ at a point $q$ of $B_x\setminus L_x$ agrees at $q$ with a function $f$ analytic on a punctured disc about $x$ containing $q$.

The steps, as in Lemma 8.1. By the identity theorem and Theorem 9.8(c), $f=\operatorname{Log}_\kappa(s-x)Y_x+H_1$ on the slit punctured disc, with $H_1$ holomorphic on the disc. $f$ and $H_1$ are continuous across the slit and $\operatorname{Log}_\kappa$ jumps by $2\pi i$, so $Y_x=0$ on the slit. The slit ends at $x$ and $Y_x$ is continuous, so $Y_x(x)=0$, which contradicts the hypothesis.

This is one step shorter than Lemma 8.1. There the hypothesis was on the derivative $X_x'(x)$, and the proof passed from "$X_x=0$ on a segment" to "$X_x\equiv0$ near $x$" by the identity theorem. Here the hypothesis is on the value, and continuity is enough.

### Proof of Theorem 1.3(a) and (b) for $G_{\log}$

Under $(\mathrm H_\infty)$, $2B_\infty=1$ and $B<1$. For (a), continuation is Theorem 9.8(b), and admissible germs exist exactly at the points of $\{\operatorname{Re}s>1\}\setminus\mathcal C_G$ by the argument used for $G_2$, with the segment $s_1+t(1+i\kappa)$, $0\le t\le2$. For (b), run the proof of Theorem 1.2 for $G$ with three replacements. Theorem 3.1 supplies $x=1+u$ in the disc with $\Theta_G(x)\ne0$, hence $Y_x(x)\ne0$ by Lemma 9.9. Theorem 9.8(b) replaces Theorem 7.4(a), so the germ of $f$ at the point $s_2$ near $x$ is $D^\kappa_{\log}+m$. And Lemma 9.10 replaces Lemma 8.1.

## Section 9.3: paths with an endpoint off the catalogue

The paper says part (c) of Theorem 1.3 is the analogue of Corollary 8.3, and gives a direct proof that uses part (b), Lemma 2.3 and the holomorphy of each series on its half-plane of absolute convergence. It first fixes what a continuation is: a continuation of a function $F$ along a path $\gamma$ is a family of functions $f_t$, $0\le t\le1$, with $f_t$ holomorphic near $\gamma(t)$, $f_0=F$ near $\gamma(0)$, and $f_{t'}=f_t$ near $\gamma(t')$ for $t'$ close to $t$; the terminal germ is that of $f_1$ at $\gamma(1)$.

This is the notion behind the chain of discs in Theorem 8.2, written with one function per time instead of one per disc. It is also the shape of the Lean definition `IsContinuationAlong` printed in the appendix.

### Proof of Theorem 1.3(c)

The paper treats $G_2$. For $G_{\log}$ replace the line $\operatorname{Re}s=\tfrac12$ and the half-plane $\operatorname{Re}s>\tfrac12$ by $\operatorname{Re}s=1$ and $\operatorname{Re}s>1$, the half-plane of absolute convergence $\operatorname{Re}s>1$ by $\operatorname{Re}s>2$, and $\mathcal C_2$ by $\mathcal C_G$. The paper notes that $\mathcal C_2$ lies in $\operatorname{Re}s\le1$, since $\operatorname{Re}x\le2$ for $x\in\Pi$, and that $\mathcal C_G$ lies in $\operatorname{Re}s\le2$.

Set-up. Let $(f_t)$ be a continuation of $G_2$ along $\gamma$, with $\operatorname{Re}\gamma(0)>1$, terminal germ $g$, and $\gamma(1)\notin\mathcal C_2$. Call a time $t$ good if there is a disc $U$ about $\gamma(t)$, inside $\operatorname{Re}s>\tfrac12$, on which $f_t$ is holomorphic and whose germ at every point of $U\setminus\mathcal C_2$ is admissible.

The plan is the usual one on an interval: show that the good times include $0$, form an open set, and form a closed set. A non-empty subset of $[0,1]$ that is both open and closed is all of $[0,1]$, because an interval is connected. Then $1$ is good.

1. Time $0$ is good. Take $U$ inside $\operatorname{Re}s>1$. That disc contains no catalogue point, $G_2$ is holomorphic on it, and every germ of $G_2$ there is admissible, by the constant path.
2. Open. If $t$ is good with disc $U$, then for $t'$ near $t$ the point $\gamma(t')$ lies in $U$ and $f_{t'}=f_t$ near it. A small disc about $\gamma(t')$ inside $U$, on which $f_{t'}=f_t$, shows that $t'$ is good.
3. Closed. Let $t_n$ be good, with discs $U_n$, and $t_n\to t^*$. There is a disc $U^*$ about $\gamma(t^*)$ on which $f_{t^*}$ is holomorphic, and for large $n$, $\gamma(t_n)\in U^*$ and $f_{t_n}=f_{t^*}$ near $\gamma(t_n)$. For such $n$, every point $w$ of $U_n\cap U^*$ off $\mathcal C_2$ and near $\gamma(t_n)$ is a point where the germ of $f_{t^*}$ is that of $f_{t_n}$, so it is admissible.
   - The limit point is not on the line. Each $\gamma(t_n)$ has real part above $\tfrac12$, so $\operatorname{Re}\gamma(t^*)\ge\tfrac12$. If it were equal to $\tfrac12$, then $U^*$ would be a disc centred on the line, containing a point $w$ with an admissible germ, and the holomorphic function $f_{t^*}$ on $U^*$ would extend that germ. Part (b) forbids this. So $\operatorname{Re}\gamma(t^*)>\tfrac12$.
   - Admissibility spreads over the disc. Shrink $U^*$ into $\operatorname{Re}s>\tfrac12$, then fix $n$ and a point $w$ as above for the smaller disc. Any point of $U^*\setminus\mathcal C_2$ is joined to $w$ by a path in $U^*\setminus\mathcal C_2$, since $\mathcal C_2$ is closed and discrete in $\operatorname{Re}s>\tfrac12$ (Lemma 2.3). Following $f_{t^*}$ along it continues an admissible germ along a path in $\{\operatorname{Re}s>\tfrac12\}\setminus\mathcal C_2$, and the result is admissible. So $t^*$ is good.
4. Conclusion. Time $1$ is good. Its disc lies in $\operatorname{Re}s>\tfrac12$ and $\gamma(1)\notin\mathcal C_2$, so the germ of $f_1$ at $\gamma(1)$, which is $g$, is admissible.

Part (b) enters only in step 3, to stop the path from reaching the boundary line. So the proof shows along the way that a path of continuation starting in the half-plane of convergence stays in the open half-plane, which is what Theorem 8.2(a) says for $G$ and $S$. The paper does not state this as a separate result for $G_2$ and $G_{\log}$.

Compare with Corollary 8.3, which was proved from Theorem 8.2 by rebuilding the path through a chain of discs. Here the open-and-closed argument obtains admissibility at off-catalogue endpoints directly from part (b). The closing remark uses the good disc to give the boundary obstruction at catalogue endpoints as well.

### The unnumbered catalogue-endpoint remark

Goodness is required on a disc at a time so it can pass through a catalogue point. At a limit of good times, the representative at the limit agrees with an earlier one near an off-catalogue point. Part (b) prevents the disc from being centred on the boundary line, and then continuation within the disc with the catalogue points removed propagates admissibility. In particular, goodness at time $1$ survives with an endpoint in the catalogue.

The remark at the end of the proof of Theorem 1.3(c) covers the remaining endpoints. If continuation exists and ends at a catalogue point, the final holomorphic representative still has a disc on which all nearby germs off the catalogue are admissible. A meromorphic extension of the terminal germ to a boundary-centred disc would agree near the endpoint and hence at some such nearby point inside both discs. That would extend an admissible germ against Theorem 1.3(b). The remark is separate from the numbered theorem. PrimePairNB checks it as `HInf.no_extension_any_path_Sq` and `HInf.no_extension_any_path_mix`, each from `Hinf` and (Z1)–(Z6).

## The closing comparison of the five series

The paper ends the section by lining up the series. For $T$ two poles meet, and the obstruction is a residue, $\Theta_G(x)$. For $G_{\log}$ a logarithm meets a pole, and the obstruction is the value $Y_x(x)=-\Theta_G(x)$. For $G$, $S$ and $G_2$ two logarithms meet, and the obstruction is the derivative $X_x'(x)$ in $v$. Its value is $\Theta_G(x)$ for $G$, $\tfrac12\Theta_S(x)$ for $S$, and $\tfrac12\Theta_2(x)$ for $G_2$. Each nonzero test is a sum over ordered pairs. Under $B<1$ Theorem 3.1 and, for $G_2$, Theorem 9.4 supply points accumulating at every point of the line. The condition $(\mathrm H_\infty)$ puts those points in the continuation region.

Table 1 pairs each type of pinch with its nonvanishing test. Theorem 4.2 gives the residue for $T$. Theorem 9.7 gives the local form for $G_{\log}$, and Theorem 6.1 gives it for $G$ and $S$, with the same calculation for $G_2$ in Section 9.1. At a point where the corresponding test is nonzero, the singular terms are a pole of $T$, then a term like $\log(s-x)$ for $G_{\log}$, then a term like $(v-x)\log(v-x)$ for $G$, $S$ and $G_2$, which is bounded but not analytic.

## Check your understanding

1. For $G_2$, which results of Sections 3 and 5 to 8 are reused as they stand, and which are replaced?
2. Why does $G_{\log}$ need no new arithmetic?
3. In the proof of Theorem 1.3(c), where is part (b) used?
4. Proposition 9.1 states its integral formula only for $2<\operatorname{Re}v<3$. Why is that enough?

Answers. (1) Reused: Theorem 3.3 and the near-pair count; Theorems 5.3, 6.1, 7.3, 7.4(a),(c) and Lemma 8.1. Replaced: the main term and the far-pair bound (Lemmas 9.2 and 9.3), which give Theorem 9.4 in place of Theorem 3.1. (2) $Y_x(x)=-\Theta_G(x)$ (Lemma 9.9), and Theorem 3.1 already gives dense points with $\Theta_G\ne0$. (3) In the closedness step, to rule out a limit point on the boundary line. (4) $D^\kappa$ and $D$ are both holomorphic on the connected half-plane $\operatorname{Re}v>2$ and agree on the strip, so they agree on the half-plane by the identity theorem.

# 10. Section 10: what more holds under RH

Section 10 explains why the near-pair count and far-pair bounds are needed in the boundary proofs under $(\mathrm H_\infty)$. Under that hypothesis, the non-cancellation argument finds a dense family using $B<1$ and $(\mathrm H_\infty)$ places it in the continuation region. For $G_2$ the corresponding far-pair estimate and dense family are Lemma 9.3 and Theorem 9.4. With RH, every pair contributing in the $G$ catalogue contains $1$, and for $x=1+u$ the point $u$ has just one squarefree representation as $1/n$ or $\rho/n$. The explicit values in equation (13) therefore give genuine singularities at every catalogue point of $G$ and $T$. Theorem 10.1 keeps RH as the hypothesis its proof uses. Sections 1.2 and 11 credit Alpöge’s proof of RH and describe its certification. Corollary 1.4 uses that certified proof in the written deduction giving the unconditional conclusions of Theorems 1.1–1.3 and 10.1.

## Equation (13), explicit values for the full catalogue

The comparison shows which part of the argument Section 3 supplies. $(\mathrm H_\infty)$ gives non-vanishing on a dense family; under RH it holds at every candidate point of $G$, because no extra pairs exist. Under RH, $(\mathrm H_\infty)$ holds and every point of $\Sigma$ other than $1$ has real part at most $\tfrac12$, so in $\operatorname{Re}s>1$ the catalogue of $G$ is
$$\mathcal C=\{2\}\cup\{1+1/k:k\ge2\text{ squarefree}\}\cup\{1+\rho/n:\rho\in\mathcal Z,\ n\ge1\text{ squarefree}\},$$
and a pair with $\operatorname{Re}(a+b)>1$ must contain $1$. Each $u=\rho/n$ has a single representation, since $\operatorname{Re}u=1/(2n)$ determines $n$. So $x=1+u$ has exactly the pairs $(1,u)$, $(u,1)$, or the single pair $(1,1)$ at $x=2$, and (7) becomes
$$X_2'(2)=1,\qquad X_{1+1/k}'(1+1/k)=2\mu(k),\qquad X_{1+\rho/n}'(1+\rho/n)=-\frac{2\mu(n)m(\rho)}\rho\ne0.\tag{13}$$

The three values, computed.

- $x=2$: one diagonal pair $(1,1)$, $c(1)^2\mathrm B(1,1)=1\cdot\Gamma(1)^2/\Gamma(2)=1$.
- $x=1+1/k$: $-2c(u)/u$ with $u=1/k$ and $c(1/k)=-\mu(k)/k$ (worked in the guide's Section 2), so $-2\cdot(-\mu(k)/k)\cdot k=2\mu(k)$, nonzero since $k$ is squarefree.
- $x=1+\rho/n$: under RH a representation $(\rho',k)$ of $u$ has $\operatorname{Re}\rho'=\tfrac12=k\operatorname{Re}u=k/(2n)$, so $k=n$ and $\rho'=\rho$. Then $c(u)=\mu(n)m(\rho)/n$ and $-2c(u)/u=-2\cdot\frac{\mu(n)m(\rho)}n\cdot\frac n\rho=-\frac{2\mu(n)m(\rho)}\rho$.

Note what changed from Section 3: $n$ need not be prime, and there is no lower bound to prove, no near pair to discard, no far pair to estimate.

## Theorem 10.1

The paper proves, under RH:

(a) Every point of $\mathcal C$ is a genuine logarithmic branch point of $G$ on every branch: every branch near $\alpha\in\mathcal C$ is $X_\alpha(s)\log(s-\alpha)$ plus a holomorphic function, with $X_\alpha$ holomorphic on $\operatorname{Re}s>1$, $X_\alpha(\alpha)=0$ and $X_\alpha'(\alpha)$ given by (13). $G$ continues along every path in $\{\operatorname{Re}s>1\}\setminus\mathcal C$ from $\operatorname{Re}s>2$, and a path along which $G$ continues never leaves this set.

(b) $T$ has a meromorphic continuation to $\operatorname{Re}s>1$ with a simple pole at every point of $\mathcal C$, of residue equal to the value in (13), and no other pole there.

### The proof

(b) is Theorem 4.2: the residue is the sum (9), which under RH is the value in (13), nonzero; and the poles lie in $\Pi\cap\{\operatorname{Re}s>1\}=\mathcal C$.

(a): the local form is Theorem 6.1 and Theorem 7.4(c), continuation along paths avoiding $\mathcal C$ is Theorem 7.4(a). The new part is that a path of continuation never touches $\mathcal C$. The steps:

1. Let $\gamma$ be a path along which $G$ continues from $\operatorname{Re}s>2$. By Theorem 8.2 it stays in $\operatorname{Re}s>1$.
2. Suppose it meets $\mathcal C$. The catalogue is relatively closed in the half-plane, so $\gamma^{-1}(\mathcal C)$ is a closed, nonempty subset of $[0,1]$, with a least element $t^*$; $t^*>0$ since the start has real part above $2$. Put $\alpha=\gamma(t^*)$. Every restriction of $\gamma$ ending before $t^*$ avoids $\mathcal C$, so its terminal germ is admissible.
3. Continuation exists at $\alpha$, so there is a holomorphic representative $f$ on a disc about $\alpha$. Shrink the disc to lie in $\operatorname{Re}s>1$, contain no other catalogue point, and sit inside the local-model disc at $\alpha$ for a generic $\kappa$.
4. For $t<t^*$ close to $t^*$, the germ at $\gamma(t)$ agrees with $f$. Join $\gamma(t)$ inside the disc minus $\alpha$ to a point $q$ off the slit; continuing as $f$ keeps the germ admissible.
5. By Theorem 7.4 the germ at $q$ is $D^\kappa+m$. But $f$ is analytic on the whole disc about $\alpha$, and $X_\alpha'(\alpha)\ne0$ by (13). Lemma 8.1 forbids this.

The paper notes this is stronger than the $(\mathrm H_\infty)$ theorem for $G$, whose proof gives non-vanishing only on a dense family, and that no such theorem is stated for $S$. The section says nothing about $G_2$ or $G_{\log}$ under RH.

## The comparison paragraph

The paper says that under RH, at $x=1+\rho/q$ with $q$ prime, only the main terms exist: $-2c(u)/u$ for $G$, and for $S$ (in $s$) $-c(u)\{K(1-\tfrac u4)+K(\tfrac12+\tfrac u4)\}$ with a nonzero bracket. So under RH the sum is an explicit nonzero factor times $c(\rho/q)=-m(\rho)/q$, the one-term case of Titchmarsh's (9.5.7), and the accumulation at the line is his (9.5.4) to (9.5.6) shifted by $1$ (then $s=(v-1)/2$ for $S$). The near-pair count and far-pair estimates exist to handle collisions that $(\mathrm H_\infty)$ permits and RH does not.

This paragraph is the clearest statement of what the paper's new arithmetic is for. Under RH the classical argument (Landau and Walfisz, as told by Titchmarsh) already gives non-vanishing. Without RH, zeros off the line create extra pairs and extra representations, and Section 3 is the price of allowing them.

# 11. Section 11: formal verification

The paper says Theorems 1.1, 1.2, 1.3, 8.2 and 10.1 and Corollary 8.3 have been checked in Lean 4 (Lean 4.34.0, Mathlib at tag v4.34.0, and the PrimeNumberTheoremAnd library). The formal theorems are implications: their hypotheses are $(\mathrm H_\infty)$ and the classical inputs (Z1) to (Z6), each written as a proposition about Mathlib's `riemannZeta` and `Gamma` and taken as a hypothesis, not an axiom. On which inputs each result uses, the paper says:

- The theorem for $S$ does not use (Z6).
- For $G_2$ and $G_{\log}$, part (a) of Theorem 1.3 uses $(\mathrm H_\infty)$, (Z1) to (Z3) and (Z6); parts (b) and (c) use $(\mathrm H_\infty)$ and all of (Z1) to (Z6). Unlike $S$, whose kernel is elementary, these two series need (Z6) already for continuation, as $G$ does, because their kernels are bounded through Stirling's formula.
- For the kernels of Sections 5 to 9, the formal proofs record the decay (K2) only in the weaker form $\mathcal K(z,v)\ll(1+|\operatorname{Im}z|)^{-2}$, which is all they use.
- Theorem 10.1 is checked from RH alone, by a different route that does not go through the sheets of Section 5.

Lean checks that these hypotheses imply the stated results. The scope also includes the catalogue-endpoint remark at the end of the proof of Theorem 1.3(c). The passage from Titchmarsh's printed statements to the forms in Section 2 is checked by hand.

Why the hypothesis lists differ between parts. Continuation and the existence of admissible germs, part (a), need the analytic machinery: the zero facts (Z1) to (Z3) behind Lemmas 2.1 and 2.2 and, for these kernels, the Gamma bound (Z6). The boundary, part (b), needs in addition the arithmetic of Section 3, which is where the zeros on the critical line (Z4) and the primes in intervals (Z5) come in. Part (c) is proved from part (b). This reading is the guide's, from where each input is used in the paper's proofs; Section 11 also explains why these two kernels need (Z6) for continuation.

The paper calls the development a standalone release, PrimePairNB version 1.2.1, under the Apache-2.0 licence and published with tag `v1.2.1`. [PrimePairNB v1.2.1](https://github.com/lpkralv/prime-pair-natural-boundaries/tree/v1.2.1)

 Its module root is `PrimePairNB`; its declarations are in the namespace `GoldbachBoundaries`, and the names in the section are relative to it: `HInf.boundary_G` means `GoldbachBoundaries.HInf.boundary_G`. The declarations the paper names:

- `Paper2.thm_boundary` for Theorem 1.1;
- `HInf.boundary_GS`, the conjunction of `HInf.boundary_G` and `HInf.boundary_S`, for Theorem 1.2;
- `HInf.boundary_Sq` and `HInf.boundary_mix` for Theorem 1.3(b) (in Lean, $G_2$ and $G_{\log}$ are `SqSer` and `MixSer`);
- `thm_A` and `rem_every_path` for $G$ and `cor_T_poles` for $T$ in Theorem 10.1;
- `HInf.exists_admS_iff`, which takes only `Hinf` and (Z1) to (Z3), for the existence of admissible germs of $S$ shown in Section 8.

Section 11 names `HInf.continuesAlong_Sq`, `HInf.continuesAlong_mix`, `HInf.exists_admSq_iff` and `HInf.exists_admMix_iff` for Theorem 1.3(a), and `HInf.every_path_Sq` and `HInf.every_path_mix` for (c). It names `HInf.every_path_stays_G`, `HInf.every_path_stays_S`, `HInf.no_extension_any_path_G`, `HInf.no_extension_any_path_S`, `HInf.cor_domain_G` and `HInf.cor_domain_S` for Theorem 8.2, and `HInf.every_path_G` and `HInf.every_path_S` for Corollary 8.3. The release's correspondence table gives the intermediate declarations and their hypotheses.

The two catalogue-endpoint declarations are `HInf.no_extension_any_path_Sq` and `HInf.no_extension_any_path_mix`. Both take `Hinf` and all six classical inputs. The formal proofs for $G_2$ instantiate the generic sheet, rotation and obstruction theorems with the kernel of Proposition 9.1, as the paper does. For $G_{\log}$ they repeat that development with $Q$ as the right factor and the pole–logarithm arc of Lemma 6.2.

The paper states that the release builds from a clean clone with the pinned versions, and that `#print axioms` on every theorem cited lists only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

Corollary 1.4 is a written deduction. Alpöge's theorem supplies RH for Theorem 10.1. Under RH every non-trivial zero has real part $\tfrac12$, so the exceptional set in $(\mathrm H_\infty)$ is empty for each $\delta>0$. That supplies the zero hypothesis for Theorems 1.1, 1.2 and 1.3. The written proofs use the applicable classical inputs (Z1)–(Z6) and the two zero-free facts following them in Section 2. In Lean, the fact that $\zeta$ has no zeros in $\Re s\ge1$ comes from Mathlib, and the release proves the absence of real zeros in $(0,1)$ from PrimeNumberTheoremAnd's Abel-summation formula.

Section 11 lists three steps taken outside Lean. The author compares the source text defining `RiemannHypothesis` in Mathlib v4.33.1, used by Alpöge with Lean v4.33.1, and Mathlib v4.34.0, used by PrimePairNB with Lean v4.34.0. The text is identical. The comparison leaves agreement of the dependent definitions and equality of the propositions across the builds unchecked in Lean. The written proof supplies the implication from RH to $(\mathrm H_\infty)$, for which the release has no declaration. Finally, the author checks the classical inputs (Z1)–(Z6) against their cited sources by hand. The two Lean developments are built and checked separately.

Section 11 reports Sutherland's independent checks as of 22 November 2026, 16:20 UTC. Completed checks included compilation of all 175,187 modules and a module-by-module `leanchecker` replay, axiom checks of the five headline theorems that listed only `propext`, `Classical.choice` and `Quot.sound`, export checks by `nanoda` and `con-leche`, comparison by `con-ron`, checks by `lean4lean` on every compiled module, and a `con-leche --compare` run against all five headline statements. An independent sandbox rebuild reproduced the export byte for byte. The versions of `con-leche` and `con-ron` bundled with Lean v4.36.0 declined with exit code 2. Full-export replays by the default and paranoid Lean kernels and the end-to-end `lake comparator` run were still in progress at that timestamp. The statement-comparison and axiom stages had passed in one comparator run. None of the reported checks had rejected the proof.

In the $(\mathrm H_\infty)$ results the kernel checks that the conclusion follows from $(\mathrm H_\infty)$ and the applicable inputs among (Z1) to (Z6). The paper supplies those classical theorems from the cited sources. Readers can compare the main formal statements printed in the appendix with the prose definitions. The primer's topic on reading Lean statements covers the notation.

## Acknowledgement and statement on the use of AI

The paper's unnumbered closing section states: the author is a computer scientist, not a mathematician; the work was his idea; he directed an AI research agent through a sequence of questions, chose the direction at each step, and decided to attack these series without RH; he designed the verification (independent adversarial reviews before results were recorded as proved, re-derivation and small-case checks, and a Lean formalization). The mathematics is largely the work of AI systems under his direction (Anthropic Claude and OpenAI models found and reviewed the arguments; Claude models drafted and edited the manuscript; AI agents wrote the Lean). He did not check the Lean line by line and relies on the kernel and the checks described; no human mathematician has checked the proof line by line; queries will be answered by him with the same AI assistance; no AI system is an author; he takes full responsibility.

# Appendix A: the Lean statements

The paper's appendix copies, verbatim from the PrimePairNB release with docstrings and proofs omitted, the definitions and the boundary statements of Theorems 1.1, 1.2 and 1.3(b). It condenses the namespace and open lines and adjusts the line breaks. The declarations are `thm_boundary`, `boundary_GS`, `boundary_Sq` and `boundary_mix`. The other declarations cited in Section 11 are in the release's correspondence table. The appendix gives a key: `Hinf` is $(\mathrm H_\infty)$; `Z1` to `Z6` are the classical inputs; `PoleSetQ` is $\Sigma$, `Pinch` is $\Pi$, and `catG`, `catS`, `catSq` are the catalogues $\mathcal C_G$, $\mathcal C_S$, $\mathcal C_2$; `G`, `T` and `Sser` (via `WS`) are the series of (1); `SqSer` and `MixSer` (via `WSq` and `Wlogq`) are $G_2$ and $G_{\log}$; for an affine map $L(s)=\ell s+\ell_0$, `Aff.HL` is $\operatorname{Re}L(s)>1$ and `Aff.RL` is $\operatorname{Re}L(s)>2$, so `Aff.twoL.HL` is $\operatorname{Re}s>\tfrac12$, `Aff.twoL.RL` is $\operatorname{Re}s>1$, `Aff.idL.HL` is $\operatorname{Re}s>1$, `Aff.idL.RL` is $\operatorname{Re}s>2$, and `catalogueL Aff.idL` is $\mathcal C_G$; `IsTerminalGerm` records continuation along a continuous path; `AdmG`, `AdmS`, `AdmSq`, `AdmMix` record admissibility; $\mathcal N\,s$ and $\mathcal N[\ne]\,s$ are a neighbourhood and a punctured neighbourhood filter; $f=^{\mathrm f}[\mathcal F]g$ is eventual equality in a filter, and with `codiscreteWithin U` it means equality in $U$ away from a set with no accumulation point there.

Three points on reading it:

- `NoMeromorphicExtensionAt` and `IsNaturalBoundary` state the boundary with "codiscrete" agreement: a meromorphic function on a disc that agrees with $F$ on the disc's part of the half-plane, except on a set with no accumulation point inside, is ruled out. That is at least as strong as "agrees on the part of the disc in the half-plane", the wording of Theorem 1.1.
- `GermExtendsMeromorphically g s₁ W` says $s_1\in W$ and some function meromorphic on $W$ equals $g$ on a punctured neighbourhood of $s_1$. This is the formal counterpart of "extends meromorphically" before Theorem 1.2.
- `IsTerminalGerm F γ g` says there is a family of functions, analytic at each point of the path and locally equal to their neighbours, starting as $F$ and ending as $g$: analytic continuation along $\gamma$ written out.

Two more, for the new series:

- The half-planes of $G_2$ and $G_{\log}$ are written through the affine map, so `AdmSq g s₁` unfolds to: there is a continuous path that stays in $\{\operatorname{Re}s>\tfrac12\}$ off `catSq`, starts in $\operatorname{Re}s>1$, ends at $s_1$, and along which `SqSer` continues with terminal germ $g$. That is the paper's definition before Theorem 1.3. `AdmMix` is the same with `MixSer`, $\operatorname{Re}s>1$ off $\mathcal C_G$, and start in $\operatorname{Re}s>2$.
- `boundary_Sq` and `boundary_mix` have the shape of the two halves of `boundary_GS`: for every admissible germ `g` at `s₁`, every real `y` and every `r > 0` with `s₁` in the ball of radius `r` about the point on the line, `g` does not extend meromorphically to that ball. All four boundary theorems take `Hinf` and `Z1` to `Z6`.

The appendix does not print the statements on the existence of admissible germs or on arbitrary paths; for those, read the release's correspondence table.

# Symbols, in order of first use

| Symbol | Where first | Meaning |
|---|---|---|
| $G$, $T$, $S$ | (1) | The first three series over ordered pairs of primes |
| $G_2$, $G_{\log}$ | §1.1 (unnumbered display) | The series over $p^2+q^2$; the series with weight $\log q$ |
| $P(z)$ | §1.1, §2.2 | Prime zeta function $\sum_pp^{-z}$ |
| $\mathcal Z$, $\rho=\beta+i\gamma$ | §1.2, §2.1 | Non-trivial zeros, each once; real and imaginary parts |
| $(\mathrm H_\infty)$ | §1.2 | Finitely many zeros with $\operatorname{Re}\rho>\tfrac12+\delta$, for each $\delta>0$ |
| $B$, $B_\infty$ | §1.2, §2.1 | Supremum of real parts of zeros; its limit as height grows |
| $\mathcal C_G$, $\mathcal C_S$ | §1.3, §2.4 | Catalogues of candidate points |
| $\mathcal C_2$ | §1.3, before Theorem 1.3 | Catalogue of $G_2$: $\{s:\operatorname{Re}s>\tfrac12,\ 2s\in\Pi\}$ |
| admissible germ | §1.3 | Germ reached along a path avoiding the catalogue |
| $Q=-P'$, $\psi=-\zeta'/\zeta$ | §1.4, §2.2 | Building block of $T$; log-derivative of $\zeta$ |
| $\Sigma$ | §§1.3 and 2.2 | $\{1/k\}\cup\{\rho/k\}$, $k$ squarefree: possible poles of $Q$ |
| $R_a$, $c(a)$ | §1.4, (2) | Residue of $Q$ at $a$; $c(a)=-R_a$ |
| $m(\rho)$, $N(t)$, $N_0(t)$ | §2.1 | Multiplicity; zero count with multiplicity; distinct zeros on the line |
| $\mathrm B(a,b)$ | §2.1 | Beta function $\Gamma(a)\Gamma(b)/\Gamma(a+b)$ |
| (Z1) to (Z6) | §2.1 | Classical inputs |
| $\mu(k)$, $\operatorname{ord}_w\zeta$ | §2.2 | Möbius function; order of $\zeta$ at $w$ |
| $F_\delta$ | Lemma 2.1 | Finite set of points of $\Sigma$ with real part above $B_\infty+\delta$ |
| $t_\delta$ | Lemma 2.2 | Height above which zeros have real part at most $B_\infty+\delta$ |
| $v$, $\mathcal V$, $\mathcal V_\infty$, $\mathcal K$, $K$, $D$ | §2.3 | Pinching variable; its domain; domain right of $2B_\infty$; kernel; $\Gamma(w)\Gamma(2-w)$; the series in $v$ |
| (K1) to (K3) | §2.3 | Kernel facts |
| $K_s(w)$ | (4) | Kernel of $T$ (same as $G$'s) |
| $\Pi$, $\mathcal X$, pairs at $x$ | §2.4 | Sums $a+b$; those right of $2B_\infty$; ordered pairs summing to $x$ |
| $J_{ab}$ | (5) | Integral of $\mathcal K$ from $a$ to $v-b$ |
| $X_x$, $M_x$ | (6) | Coefficient function at $x$; $2\pi iX_x$ |
| $\Theta_G$, $\Theta_S$ | Theorem 3.1 | The two sums over pairs |
| representation, good pair, $J$, $M$, $\mathcal P(X)$ | §3.1 | $(\rho',k)$ with $\rho'/k=u$; single-representation pair; window; $\lceil2\log X/A_0\rceil$; candidate pairs |
| $\zeta^*$, $d$ | Lemma 3.2 | The off-line zero forced by a second representation; reduced denominator |
| $H$, $Y$, $n_0$ | §3.2, §3.3 | Height cutoff $2\log X$; height bound $y+1$; denominator bound |
| $F$, $c$, $I_c$, $[A]$, $g_s$ | Theorem 4.1 | $F_\delta$; contour abscissa; line integral; indicator; integrand |
| $\nu(x)$ | Theorem 4.2 | Constant indicator weights near $s_0$ |
| $\kappa$, $e$, $\theta$ | §5.1 | Slope; unit direction $e^{i\theta}$; its angle |
| height, abscissa, east, $\kappa$-line | §5.1 | Coordinates after dividing by $e$ |
| generic $\kappa$ | §5.1 | No two points of $\Sigma$, or of $\Pi$, on one $\kappa$-line |
| $\operatorname{Log}_\kappa$ | §5.1 | Logarithm cut along the ray $-e[0,\infty)$ |
| $\ell_a$, $U_\kappa$, $P^\kappa$ | §5.1 | Westward cut from $a$; cut half-plane; branch of $P$ on it |
| $E_a$ | Lemma 5.1 | Holomorphic remainder at $a$ |
| $L_x$, $\Omega_\kappa$ | §5.2 | Westward cut from $x$; cut domain of the sheet |
| separating $\kappa$-graph $\Gamma$ | §5.2 | Contour between left and right points |
| $D^\kappa$ | (11) | The sheet |
| $\Gamma_0$, $\Gamma_{\mathrm{out}}$, $r_0$, $r$ | Theorem 6.1 proof | Graph through collisions; it minus flat tops; band size; disc radius |
| $\delta$, $t$, $\epsilon$, $A_\epsilon$, $A^E$ | Theorem 6.1 proof | $v-x$; local coordinate; $\delta/e$; separating arc; fixed eastern polygon |
| $f(t,\mu)$, $\Phi$, $\mathcal P$, $\mathcal R$, $h$ | Theorem 6.1 proof | Local kernel; pinch integral; $\int_0^\epsilon f$; remainder; fixed-arc integral |
| $H$ (again) | (12) | Holomorphic remainder in the local model |
| critical direction | §7 opener | Direction whose eastward ray from $v_1$ meets $\mathcal X$ |
| $\mathcal M$, $C$ | before Theorem 7.4 | Integer combinations of the $M_x$; constant (only for $S$) |
| $\mathsf R$, $\mathsf V$, $\tilde h$, $\varphi$ | Theorem 7.4(b) proof | $\operatorname{Re}v>2$; $\mathcal V_\infty$; continued correction; meromorphic extension of $h'$ |
| $B_x$ | Theorem 7.4(c) | Local-model disc at $x$ |
| $\Delta$, $E$, $\alpha$, $\Delta_\alpha$ | proof of Theorem 1.2 | Proposed disc; pole set; candidate point in $s$; local disc |
| $\Theta_2$ | Lemma 9.2 | The sum over pairs for $G_2$, with weight $\mathrm B(a/2,b/2)$ |
| $D^\kappa_{\log}$ | Theorem 9.6 | The sheet of $G_{\log}$ |
| $Y_x$ | Theorem 9.7 | Coefficient of the logarithm for $G_{\log}$ |
| $\mathcal M_{\log}$ | before Theorem 9.8 | Integer combinations of the $2\pi iY_x$ |
| continuation $(f_t)$, good time | §1.3 (continuation), §9.3 (restatement and good times) | Family of local functions along a path. A time is good if the representative is holomorphic on a disc about the current point in the open continuation half-plane and its germs at all points of that disc off the catalogue are admissible |
| $\mathcal C$ | §10 | Catalogue of $G$ under RH |
