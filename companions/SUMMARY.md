---
title: "Paper A: an executive summary"
subtitle: "Natural boundaries of prime-pair Dirichlet series"
author: "For the author"
date: "24 November 2026, for the paper as posted"
---
This is the author's summary of *Natural boundaries of prime-pair Dirichlet series*. It describes the current five-series paper, the written deduction of the unconditional results, and the Lean development that checks the implications used in that deduction.

## 1. What was proved

First in plain words. Take two primes $p$ and $q$ and form a Dirichlet series by summing a weight
over every ordered pair. Five series are studied:

$$G(s)=\sum_{p,q}\frac1{(p+q)^s},\qquad
T(s)=\sum_{p,q}\frac{\log p\,\log q}{(p+q)^s},\qquad
S(s)=\sum_{p,q}\frac{p^{1-s}q^{2-s}}{(p^2+q^2)^2},$$

$$G_2(s)=\sum_{p,q}\frac1{(p^2+q^2)^s},\qquad
G_{\log}(s)=\sum_{p,q}\frac{\log q}{(p+q)^s}.$$

$G$ and $T$ count the ways to write a whole number as a sum of two primes, without and with the
logarithmic weights of the Goldbach problem; both converge for $\Re s>2$. $S$ converges for
$\Re s>\tfrac12$ and tests the method on a different kernel: its summand is not symmetric in $p$
and $q$, its kernel decays at half the rate of the kernel of $G$, and its contour formula holds
only on a strip. $G_2$ converges for $\Re s>1$; it has a third kernel and its boundary on a
different line. $G_{\log}$ converges for $\Re s>2$; it carries the logarithmic weight on one prime
only, so it lies between $G$ and $T$.

Each series continues some way to the left of where it first converges. The question is whether it
can be continued across a certain vertical line. A line is a *natural boundary* when the function
cannot be continued across it at any point. The paper proves that $\Re s=1$ is a natural boundary
of $T$, of $G$ and of $G_{\log}$, that $\Re s=\tfrac12$ is one of $G_2$, and that $\Re s=0$ is one
of $S$. These conclusions hold unconditionally by Corollary 1.4. For $T$, which is single-valued, this is the usual statement. The other four are
many-valued, because they carry logarithmic singularities, and for them the boundary is proved on
*every branch*. If that proof were withdrawn, Theorems 1.1–1.3 would still stand under $(\mathrm H_\infty)$ and Theorem 10.1 under RH.

The boundary theorems isolate the property of the zeros their proofs use. Their hypothesis allows off-line zeros and leaves the ordinates of the zeros of $\zeta$ unrestricted. The earlier
arguments it builds on, by Egami and Matsumoto and by Bhowmik and Schlage-Puchta for the von
Mangoldt-weighted series, remove competing terms by a hypothesis on additive relations among the
ordinates. This paper assumes only:

> $(\mathrm H_\infty)$: for every $\delta>0$, only finitely many non-trivial zeros $\rho$ of $\zeta$
> have $\Re\rho>\tfrac12+\delta$.

Section 1.2 displays the implications
$$\mathrm{RH}\Longrightarrow(\mathrm H_\infty)\Longrightarrow\text{Lindelöf hypothesis},\qquad(\mathrm H_\infty)\Longrightarrow B<1,$$
where $B$ is the supremum of the real parts of the zeros. $(\mathrm H_\infty)$ already follows
from the statement that only finitely many zeros lie off the critical line, so it allows exceptions
to RH. The second implication uses Backlund's criterion. The paper takes RH as proved on the basis of the certified Lean proof described below.

The zero hypothesis is used at two strengths. The arithmetic in Section 3 and the corresponding argument for $G_2$ in Section 9.1 need only $B<1$, where $B$ is the supremum of the real parts of the non-trivial zeros. The analytic construction starts from the classical inputs. Its contour bounds depend on the locations of the zeros, and its domain is governed by $B_\infty$, the limiting supremum at large absolute height. In the collision variable $v$ the left edge is $\Re v=2B_\infty$. This gives a half-plane for four series and a strip for $S$. The condition $(\mathrm H_\infty)$ sets $2B_\infty=1$ and thereby places that edge on the boundary line in each series' own variable. The paper leaves open what continuation $B<1$ alone would give up to those lines.

In precise terms, Corollary 1.4 gives the conclusions of Theorems 1.1, 1.2, 1.3 and 10.1 unconditionally. The statements below give the domains, germ conditions and catalogue conclusions to which the corollary applies. Write $P(z)=\sum_p p^{-z}$ for the prime zeta
function and $Q=-P'$; the singularities of the series come, in pairs, from those of $P$ and $Q$.
Let $\Sigma$ be the set of candidate singular points of $P$ and $\Pi=\Sigma+\Sigma$. Each
many-valued series has a set of candidate singular points, its *catalogue*, closed and discrete
under $(\mathrm H_\infty)$:
$\mathcal C_G=\Pi\cap\{\Re s>1\}$ for $G$ and for $G_{\log}$,
$\mathcal C_S=\{s:\Re s>0,\ 2s+1\in\Pi\}$ for $S$, and
$\mathcal C_2=\{s:\Re s>\tfrac12,\ 2s\in\Pi\}$ for $G_2$.
A germ of $G$ at a point is *admissible* if it is reached from $\Re s>2$ by continuation along a
path in $\{\Re s>1\}\setminus\mathcal C_G$; the same definition serves $G_{\log}$. A germ of $G_2$
is admissible if it is reached from $\Re s>1$ along a path in $\{\Re s>\tfrac12\}\setminus\mathcal
C_2$. A germ of $S$ is admissible if it is reached from $\Re s>1$ along a path in
$\{\Re s>0\}\setminus\mathcal C_S$ along which continuation exists.

**Theorem 1.1 (the series $T$).** Assume $(\mathrm H_\infty)$. Then $T$ has a single-valued
meromorphic continuation to $\Re s>1$. Every disc centred on a point of $\Re s=1$ contains infinitely
many poles of this continuation, so no function meromorphic on such a disc agrees with the
continuation on the part of the disc in $\Re s>1$.

**Theorem 1.2 (the series $G$ and $S$).** Assume $(\mathrm H_\infty)$. No admissible germ of $G$ at a
point inside a disc centred on $\Re s=1$ extends meromorphically to that disc. The same holds for an
admissible germ of $S$ and a disc centred on $\Re s=0$.

The statement for $S$ is not empty. Section 8 of the paper shows, before the proof of Theorem 1.2,
that under $(\mathrm H_\infty)$ an admissible germ of $S$ exists at every point of $\Re s>0$ off the
catalogue, so every disc centred on the line contains base points of such germs. The Lean
declaration is `HInf.exists_admS_iff`, which takes only $(\mathrm H_\infty)$ and (Z1) to (Z3).

**Theorem 1.3 (the series $G_2$ and $G_{\log}$).** Assume $(\mathrm H_\infty)$.

- (a) $G_2$ continues analytically along every path in $\{\Re s>\tfrac12\}\setminus\mathcal C_2$
  starting in $\Re s>1$, and $G_{\log}$ along every path in $\{\Re s>1\}\setminus\mathcal C_G$
  starting in $\Re s>2$. A point carries an admissible germ of $G_2$ if and only if it lies in
  $\{\Re s>\tfrac12\}\setminus\mathcal C_2$, and one of $G_{\log}$ if and only if it lies in
  $\{\Re s>1\}\setminus\mathcal C_G$.
- (b) No admissible germ of $G_2$ at a point inside a disc centred on $\Re s=\tfrac12$ extends
  meromorphically to that disc. The same holds for an admissible germ of $G_{\log}$ and a disc
  centred on $\Re s=1$.
- (c) A path that starts in $\Re s>1$, along which $G_2$ continues analytically, and that ends off
  $\mathcal C_2$ has an admissible terminal germ. The same holds for $G_{\log}$, with start in
  $\Re s>2$ and endpoint off $\mathcal C_G$.

The remark at the end of the proof of Theorem 1.3(c) covers the remaining endpoints. If continuation exists and ends at a catalogue point, the final holomorphic representative still has a disc on which all nearby germs off the catalogue are admissible. A meromorphic extension of the terminal germ to a boundary-centred disc would agree near the endpoint and hence at some such nearby point inside both discs. That would extend an admissible germ against Theorem 1.3(b). The remark is separate from the numbered theorem. PrimePairNB checks it as `HInf.no_extension_any_path_Sq` and `HInf.no_extension_any_path_mix`, each from `Hinf` and (Z1)–(Z6).

**Theorem 8.2 (arbitrary paths, for $G$ and $S$).** Assume $(\mathrm H_\infty)$. A path along which
$G$ continues analytically from $\Re s>2$ stays in $\Re s>1$, and if its endpoint lies in a disc
centred on the line, the terminal germ does not extend meromorphically to that disc, with no
condition on the endpoint. The same holds for $S$ with start in $\Re s>1$, confinement to
$\Re s>0$, and the line $\Re s=0$. And no connected open set that contains the base point of an
admissible germ and meets the boundary line carries a meromorphic function with that germ.

**Corollary 8.3.** Assume $(\mathrm H_\infty)$. A path along which $G$ continues from $\Re s>2$ and
which ends off $\mathcal C_G$ has an admissible terminal germ; the same for $S$.

**Theorem 10.1 (what more holds under RH).** Assume RH. By Theorem 10.1(a), every point of the $G$
catalogue is a genuine logarithmic branch point of $G$ on every branch, with the derivative of
the coefficient at the point given explicitly for each of the three kinds of catalogue point.
The same part states that $G$ continues along every path in $\Re s>1$ that avoids the catalogue
and starts in $\Re s>2$. Any path along which $G$ continues from $\Re s>2$ stays in $\Re s>1$ and
avoids the catalogue. Part (b) states that $T$ has a meromorphic continuation to $\Re s>1$ with a simple pole, of the corresponding residue, at every
catalogue point and no other. This is stronger than what $(\mathrm H_\infty)$ gives for $G$, whose
proof yields non-vanishing only on a dense family of points. Theorem 10.1 concerns $G$ and $T$; the
paper says it states no such theorem for $S$.

Corollary 1.4 is a written deduction. Alpöge's theorem supplies RH for Theorem 10.1. Under RH every non-trivial zero has real part $\tfrac12$, so the exceptional set in $(\mathrm H_\infty)$ is empty for each $\delta>0$. That supplies the zero hypothesis for Theorems 1.1, 1.2 and 1.3. The written proofs use the applicable classical inputs (Z1)–(Z6) and the two zero-free facts following them in Section 2. In Lean, the fact that $\zeta$ has no zeros in $\Re s\ge1$ comes from Mathlib, and the release proves the absence of real zeros in $(0,1)$ from PrimeNumberTheoremAnd's Abel-summation formula.

Section 11 lists three steps taken outside Lean. The author compares the source text defining `RiemannHypothesis` in Mathlib v4.33.1, used by Alpöge with Lean v4.33.1, and Mathlib v4.34.0, used by PrimePairNB with Lean v4.34.0. The text is identical. The comparison leaves agreement of the dependent definitions and equality of the propositions across the builds unchecked in Lean. The written proof supplies the implication from RH to $(\mathrm H_\infty)$, for which the release has no declaration. Finally, the author checks the classical inputs (Z1)–(Z6) against their cited sources by hand. The two Lean developments are built and checked separately.

The conditional implications are checked in Lean as implications with their respective inputs. Corollary 1.4 proves the unconditional result by the written deduction above. The paper also uses Alpöge's certified Lean proof of RH to supply the additional zero hypothesis wherever a statement below assumes RH, $(\mathrm H_\infty)$ or $B<1$, with its other conditions in force.

Section 10 explains why the near-pair count and far-pair bounds are needed in the boundary proofs under $(\mathrm H_\infty)$. Under that hypothesis, the non-cancellation argument finds a dense family using $B<1$ and $(\mathrm H_\infty)$ places it in the continuation region. For $G_2$ the corresponding far-pair estimate and dense family are Lemma 9.3 and Theorem 9.4. With RH, every pair contributing in the $G$ catalogue contains $1$, and for $x=1+u$ the point $u$ has just one squarefree representation as $1/n$ or $\rho/n$. The explicit values in equation (13) therefore give genuine singularities at every catalogue point of $G$ and $T$. Theorem 10.1 keeps RH as the hypothesis its proof uses, and Corollary 1.4 supplies it.

## 2. Why it matters

Without the Riemann Hypothesis, several singular points of the prime zeta function can sum to the
same point, and their contributions might cancel. This paper keeps no hypothesis that rules such
coincidences out. At the points selected by the counting argument, $x=1+\rho/q$, with $\rho$ on the critical line and $q$
prime, the prime-zeta coefficient at $\rho/q$ reduces to a single Möbius term. The collision sum still has the two main ordered pairs and can have extra pairs. The scaled zeros $\rho/q$ are so abundant
across primes in a window that the zeros of $\zeta$ cannot cancel all of them. A count of near
pairs removes the few bad points, and the decay of the Gamma factors controls the pairs of large
height. The analytic half turns a non-zero coefficient into an obstruction to continuation that
holds on every branch: the plane is cut along parallel rays to build a single-valued sheet, and
rotating the cut direction never changes the local coefficient at a candidate point.

The calculation in Section 6 isolates each collision with a short contour arc. The outer contour passes through the collision points at $v=x$ and separates the other left and right points. After the small pieces around collisions are removed, the rest has enough clearance to stay fixed as $v$ changes near $x$. Its integral is holomorphic there. Each short arc accounts for one ordered pair and yields its own logarithmic term. This explains why the coefficient is a finite sum of pair integrals for two logarithms and a finite sum of kernel values when a logarithm meets a pole.

Section 7 explains the excursion by tracking a derivative. On the right of the strip the convergent series $D$ is still holomorphic. The correction to $D$ leaves as $h=m+C$, whose derivative $m'$ is meromorphic on the whole plane. If the germ continues, subtracting $D$ along the excursion continues $h$. Uniqueness of continuation fixes the derivative of that correction to $m'$, so on re-entry the correction differs from $h$ by a constant. This is the source of the $C$ allowed in Theorem 7.4(b).

There are two path statements. The sheet construction describes a germ reached along a path avoiding the candidate points in its domain. For $S$, Theorem 7.4(b) also permits excursions out of the strip to the right, provided continuation exists and the path ends back in the strip. Under $(\mathrm H_\infty)$ the boundary argument handles arbitrary paths of analytic continuation. Corollary 8.3 for $G,S$ and Theorem 1.3(c) for $G_2,G_{\log}$ give admissibility when the endpoint lies off the catalogue. At a catalogue endpoint, the boundary obstruction instead uses an admissible germ at a nearby point in the same holomorphic representative.

The two further series show which layer of the argument depends on what. For $G_2$ the kernel changes
and the analytic sections apply as they stand, so only the arithmetic sum changes and the counting
argument is run again for it. For $G_{\log}$ one factor of the integrand has poles where the other
has logarithms, so the local calculation becomes a residue, and the quantity that must not vanish
is minus the sum already controlled for $G$ and $T$; no new arithmetic is needed. The paper closes
Section 9 by comparing the three types of collision. For $T$ two poles meet and the obstruction is a residue. For
$G_{\log}$ a logarithm meets a pole and the obstruction is a value of the coefficient. For $G$, $S$ and
$G_2$ two logarithms meet and the obstruction uses the derivative of the coefficient in $v$. This derivative is $\Theta_G(x)$ for $G$, $\tfrac12\Theta_S(x)$ for $S$, and $\tfrac12\Theta_2(x)$ for $G_2$. The names $\Theta_G$, $\Theta_S$ and $\Theta_2$ denote the corresponding weighted sums over ordered colliding pairs.

The sign check in Section 9.2 starts from $A(X)=\sum_{p+q\le X}\log q=\sum_{p\le X}\vartheta(X-p)$, where $\vartheta(y)=\sum_{q\le y}\log q$. The prime number theorem gives $\vartheta(y)=y+o(y)$. For any chosen relative error, choose a fixed cutoff above which this error bound holds. Below that cutoff the total error is $O(\pi(X))$, where $\pi(t)$ counts primes up to $t$. Thus $A(X)$ is asymptotic to $\sum_{p\le X}(X-p)=\int_2^X\pi(t)\,dt\sim X^2/(2\log X)$. Partial summation then writes $G_{\log}(2+\delta)$ as $(2+\delta)\int_4^\infty A(t)t^{-3-\delta}\,dt$. The substitution $t=e^y$ leads to $\int_{\log4}^\infty e^{-\delta y}\,dy/y$, which grows like $-\log\delta$ as $\delta\to0^+$. This agrees with $Y_2(2)=-1$ in the local model when $B_\infty<1$. The paper uses the calculation to check the sign and normalization.

The paper credits the work it builds on. The natural boundary of the prime zeta function is the
theorem of Landau and Walfisz, credited as Titchmarsh and Dahlquist credit it; Kluyver had asserted
it under RH without details, and Landau proved it under RH. The denominator step in the
non-vanishing of the coefficient is Titchmarsh's proof of his (9.5.7). For Euler products
$\prod_ph(p^{-s})$ the paper cites Dahlquist's theorem and, through Dahlquist, Estermann's earlier
treatment of polynomial $h$ with integer coefficients. Isolating a main pair of zeros and bounding
the rest by Gamma decay is Egami and Matsumoto's; comparing a main term with far pairs is Bhowmik
and Schlage-Puchta's. Both remove near pairs by a hypothesis on additive relations among ordinates,
which the paper states in Bhowmik and Schlage-Puchta's form and connects to a remark of Fujii; the
paper's count takes the place of that hypothesis in its own setting and says nothing about it in
theirs. The idea that zeros scaled by $1/p$ are too many to be cancelled is Bhowmik and
Schlage-Puchta's earlier one, for Euler products of shifted zeta factors. Separating contours for a
multiplicative kernel go back to Hadamard and Borel, and cut domains to Hadamard. The paper cites Pham for the local jump of
a pinched integral and cites his mixed case, a polar locus meeting a ramified one, at
the pole–logarithm lemma used for $G_{\log}$; for Hadamard products the paper cites Pérez-Marco.
Resurgence theory (Sauzin; Ou and Delabaere) is cited as the setting where singularities at sums of
singular points are standard, and no theorem from it is used. The contour shift for $T$ parallels
Egami and Matsumoto's proof for the von Mangoldt-weighted series. The Mellin–Barnes integrals for
$G_2$ and $G_{\log}$ come from the same formula of Egami and Matsumoto.

The paper also says which nearby results do not apply, and why. The theorems of Tanigawa and Zhai
and of Peter, on Dirichlet series attached to polynomials, ask for auxiliary series meromorphic on
the whole plane, which $P$ and $Q$ are not. Results for series weighted by the von Mangoldt
function do not transfer when the sums over prime powers are replaced by sums over primes. Matsumoto's survey, Egami and Matsumoto's
function-field analogue, and the double series of Matsumoto, Nawashiro and Tsumura are cited for
context. So is a preprint in which Li and Liu state that they derive the binary Goldbach conjecture for large
even integers from the Generalized Riemann Hypothesis for Dirichlet $L$-functions together with either of two
further spectral hypotheses; it concerns representation counts of individual integers, not the
continuation of the generating series.

Two published statements about the squares case meet the paper's result. For the weighted analogue
$\sum\Lambda(m)\Lambda(n)(m^2+n^2)^{-s}$, Tanigawa and Zhai state that under RH it continues
meromorphically only to $\Re s>\tfrac12$, and Egami and Matsumoto wrote that the proof of the
natural-boundary claim of Tanigawa and Zhai's Theorem 1.3 "seems incomplete"; the paper reports both. El-Gammal studies $G_2$ itself
and conjectures that it continues meromorphically to at least $\Re s>0$.

Section 1.5 refutes El-Gammal's Conjecture 7.8 without any hypothesis on the zeros. The prime number theorem gives a count of order $X/\log^2 X$ for the ordered pairs with $p^2+q^2\le X$. Partial summation gives convergence at $s=1$ and divergence at every real $s<1$. The coefficients are nonnegative, so Landau's theorem makes $s=1$ singular. The finite limit $G_2(1)$ along the real axis from the right excludes a pole. This rules out a single meromorphic continuation to $\Re s>0$. The point $s=1$ belongs to $\mathcal C_2$ because $2=1+1\in\Pi$. Paths can cross $\Re s=1$ at points off the catalogue as in Theorem 1.3(a), and the every-branch boundary is $\Re s=\tfrac12$. The argument at $s=1$ is outside the Lean release.

On novelty, the paper states that it knows of no earlier proof of Theorems 1.1, 1.2 or 1.3 under
this hypothesis, nor of a boundary for $G$, $S$, $G_2$ or $G_{\log}$ on every branch.

## 3. How it was found

Starting the work was the author's idea. He is a computer scientist, not a mathematician. He directed
an AI research agent through a sequence of questions on natural boundaries of prime-only Goldbach
series, chose at each step the direction to pursue, and decided to attack these series without the
Riemann Hypothesis. He designed the verification: independent adversarial reviews of the results
before they were recorded as proved, with re-derivation and small-case checks where those apply, and
a formalization in Lean.

The mathematics is largely the work of AI systems under his direction. Anthropic Claude models and
OpenAI models found and reviewed the arguments; one Claude model drafted the manuscript and another
edited it; AI agents wrote the Lean development. The author did not write or check the Lean
development line by line; he relies on the Lean kernel and the checks described below. No human
mathematician has checked the proof line by line. No AI system is an author, and the author takes
full responsibility for the content.

## 4. How it was checked

- **Formal verification.** Theorems 1.1, 1.2, 1.3, 8.2 and 10.1 and Corollary 8.3 are checked in
  Lean 4, together with the catalogue-endpoint remark after Theorem 1.3(c) (Lean v4.34.0, Mathlib at tag v4.34.0, PrimeNumberTheoremAnd). The formal theorems are
  implications. The boundary and path statements take $(\mathrm H_\infty)$ and the applicable inputs among
  $(\mathrm Z1)$ to $(\mathrm Z6)$, formulated with Mathlib definitions such as `riemannZeta` and
  `Gamma`. Lean takes each input as a hypothesis of the implication. The theorem for $S$ does not use
  $(\mathrm Z6)$. For $G_2$ and $G_{\log}$, part (a) of Theorem 1.3 uses $(\mathrm H_\infty)$,
  $(\mathrm Z1)$ to $(\mathrm Z3)$ and $(\mathrm Z6)$, and parts (b) and (c) use
  $(\mathrm H_\infty)$ and all six. Theorem 10.1 is checked from RH alone, by a different route
  that does not go through the sheets. Two further classical facts (no zero of $\zeta$ on
  $\Re s\ge1$, no real zero in $(0,1)$) come from Mathlib for the first fact and from the release's proof using PrimeNumberTheoremAnd for the second. The formal proofs
  record the kernel decay (K2) only in a weaker polynomial form, which is all they use. What is
  machine-checked is that the hypotheses imply the stated results. Whether the formal definitions
  say what the prose says is a matter of reading them, and the paper's appendix prints the
  definitions and the boundary statements of Theorems 1.1, 1.2 and 1.3(b) for that purpose.
- **Lean names the paper gives.** `Paper2.thm_boundary` for Theorem 1.1; `HInf.boundary_GS`, the
  conjunction of `HInf.boundary_G` and `HInf.boundary_S`, for Theorem 1.2; `HInf.boundary_Sq` and
  `HInf.boundary_mix` for Theorem 1.3(b); `thm_A` and `rem_every_path` (for $G$) and `cor_T_poles` (for $T$) for
  Theorem 10.1; `HInf.exists_admS_iff` for the existence of admissible germs of $S$. In Lean,
  $G_2$ and $G_{\log}$ are `SqSer` and `MixSer`. Section 11 names `HInf.continuesAlong_Sq`, `HInf.continuesAlong_mix`, `HInf.exists_admSq_iff` and `HInf.exists_admMix_iff` for Theorem 1.3(a), and `HInf.every_path_Sq` and `HInf.every_path_mix` for (c). It names `HInf.every_path_stays_G`, `HInf.every_path_stays_S`, `HInf.no_extension_any_path_G`, `HInf.no_extension_any_path_S`, `HInf.cor_domain_G` and `HInf.cor_domain_S` for Theorem 8.2, and `HInf.every_path_G` and `HInf.every_path_S` for Corollary 8.3. The release's correspondence table gives the intermediate declarations and their hypotheses.

- **Release.** The standalone PrimePairNB release is Apache-2.0, with module root `PrimePairNB` and declarations in the namespace `GoldbachBoundaries`. It builds from a clean clone with pinned versions. On every theorem cited in Section 11, `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. The public release uses the tag `v1.2.1`. [PrimePairNB v1.2.1](https://github.com/lpkralv/prime-pair-natural-boundaries/tree/v1.2.1)

On 20 November 2026 Alpöge announced a Lean proof of RH and of GRH for Dirichlet $L$-functions, in a library of about 17 million lines without an accompanying prose proof. The joint Lean and Mathlib statement, endorsed by the Lean FRO and the Mathlib Initiative on 21 November 2026, certifies the RH statement and proof. The joint statement reports that two independent tools confirmed that the theorem proved is exactly Mathlib's `RiemannHypothesis`. It also reports that Lean's official kernel checked the proof and that other checkers accepted it. The paper takes RH as proved on the strength of the cited certification and checks. The author read the headline statements and scanned the library's source, and relies on the cited checks for the build and proof.

Section 11 reports Sutherland's independent checks as of 22 November 2026, 16:20 UTC. Completed checks included compilation of all 175,187 modules and a module-by-module `leanchecker` replay, axiom checks of the five headline theorems that listed only `propext`, `Classical.choice` and `Quot.sound`, export checks by `nanoda` and `con-leche`, comparison by `con-ron`, checks by `lean4lean` on every compiled module, and a `con-leche --compare` run against all five headline statements. An independent sandbox rebuild reproduced the export byte for byte. The versions of `con-leche` and `con-ron` bundled with Lean v4.36.0 declined with exit code 2. Full-export replays by the default and paranoid Lean kernels and the end-to-end `lake comparator` run were still in progress at that timestamp. The statement-comparison and axiom stages had passed in one comparator run. None of the reported checks had rejected the proof.

- **Works considered and not cited.** A sieve paper of Li and Liu (a different problem);
  Matsumoto's 2007 survey in Japanese (its results are in the two cited sources); Matsumoto and
  Tanigawa 2003 and Katsurada 2012 (the Mellin–Barnes step they illustrate is credited where it is
  used, and their theorems do not apply to $P$ or $Q$).

## 5. Where everything is

- The paper opens with the five series, the zero hypothesis and Corollary 1.4 in Section 1. Table 1 is the strategy map. Table 2, in Section 2, collects the notation. Section 2 also gives the classical inputs, the candidate points and the kernels.
- Section 3 proves the arithmetic non-cancellation. Section 4 gives the single-valued continuation and boundary for $T$. Sections 5 through 7 build the sheets, compute the local logarithm and compare reached branches.
- Section 8 proves the boundary and the arbitrary-path results for $G$ and $S$. Section 9 treats $G_2$ and $G_{\log}$, including the catalogue-endpoint remark. Section 10 describes the full catalogue for $G$ and the poles of $T$ using RH.
- Section 11 gives the verification scope, the separate Lean builds, and the steps joining them. Appendix A prints the formal definitions and four boundary declarations. The public release contains the correspondence table and the instructions for the pinned build and axiom check. [PrimePairNB v1.2.1](https://github.com/lpkralv/prime-pair-natural-boundaries/tree/v1.2.1)
- The primer teaches the background, and the reading guide follows the paper statement by statement.

## 6. What is open, and the limits

- The natural-boundary conclusions are unconditional. The three steps outside Lean are the comparison of the two Mathlib versions, RH implying $(\mathrm H_\infty)$, and the use of the classical inputs. The passage from Titchmarsh's statements to the forms used in Section 2 is checked by hand. PrimePairNB checks the implications with the applicable classical results as hypotheses. The formal proof of RH on which the written deduction relies was released without an accompanying prose proof. If that proof were withdrawn, Theorems 1.1–1.3 would still stand under $(\mathrm H_\infty)$ and Theorem 10.1 under RH.
- No human mathematician has checked the proof line by line. Queries about the proof will be
  answered by the author, with the same AI assistance.
- The arithmetic theorem needs only $B<1$, but the paper does not show that $B<1$ alone gives
  continuation up to the boundary lines.
- Theorem 7.4 describes a family containing the germs reached along the specified paths for $G,S$. Section 9 gives the corresponding descriptions for $G_2,G_{\log}$. Under $(\mathrm H_\infty)$ these descriptions cover arbitrary arrival paths at endpoints off the catalogue in the sheet domain. It does
  not claim that every member of the family is reached, so it does not classify the monodromy.
- Under $(\mathrm H_\infty)$ the non-vanishing is proved at a dense family of candidate points, not
  at all of them: a catalogue point where the coefficient vanishes identically is not excluded.
- For $G_2$ and $G_{\log}$ the catalogue-endpoint remark gives the arbitrary-terminal-germ obstruction on discs, as Theorem 8.2(a) does for $G$ and $S$. The connected-open-set statement in Theorem 8.2(b) is stated for $G$ and $S$. Theorem 10.1's full-catalogue statement concerns $G$ and $T$.
- Toma's thesis is unread.
- Public posting, and any contact with an expert, are the author's decisions; nothing is posted
  without his explicit approval.
