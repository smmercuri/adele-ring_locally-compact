# Local Compactness of the Adele Ring of a Number Field

This repository contains the proof that the adele ring of a number field is locally compact, formalised in Lean 4.7.0 using Mathlib's version [eaede86](https://github.com/leanprover-community/mathlib4/tree/eaede86aa7777630a3826cd8f3fbf0cbaafa53e6).

That the adele ring of a number field is locally compact is one of the motivators for defining the adele ring using the _restricted_ direct product over all completions, rather than just the usual direct product. Moreover, this allows one to do harmonic analysis over the subgroup of units of the adele ring which was done in Tate's landmark thesis, a precursor to the Langlands program. 

This work follows on from prior work of Maria Inés de Frutos-Fernández, who first formalised the definition of the adele ring of a global field [here](https://github.com/mariainesdff/ideles/tree/journal-submission), some of which has been ported to Mathlib's version [eaede86](https://github.com/leanprover-community/mathlib4/tree/eaede86aa7777630a3826cd8f3fbf0cbaafa53e6), and we also use some results from their recent work with Filippo A. E. Nuccio [here](https://github.com/mariainesdff/local_fields_journal/tree/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3), namely we port some foundational results on discrete valuations.

## Overview of the proof

### Introduction

Let $K$ be an algebraic number field over $\mathbb{Q}$, then its ring of integers $O$ is a Dedekind domain of Krull dimension $1$. By the extension of Ostrowski's theorem to number fields any valuation on $K$ is equivalent to some $\mathfrak{p}$-adic valuation on $K$ or an absolute value arising from the real and complex embeddings of $K$. Equivalence classes of valuations on $K$ are known as _places_. Thus places of $K$ are indexed by the real/complex embeddings of $K$ and by the primes $\mathfrak{p}$ of $O$; the former are called the _infinite_ places and the latter the _finite_ places. 

Let $v$ be a place of $K$, then we denote by $K\_v$ the completion of $K$ with respect to some representative valuation of the place $v$. The place $v$ extends naturally to a place on $K\_v$, which we denote by $|\cdot|\_v$. The integral closure of $O$ inside $K\_v$ is called the ($v$-adic) ring of integers and is denoted $O\_v$; this corresponds with the ring of all $x \in K\_v$ such that $|x|_v \le 1$. 

The direct product of completions of $K$ at finite places is denoted $$\widehat{K} := \prod\_{v\ \text{finite}} K\_v.$$ This product is _not_ locally compact, given the product topology. On the other hand, we define the _finite adele ring_ as the _restricted_ direct product $$\mathbb{A}\_{K, f} = \prod\_{v\ \text{finite}}{'}(K\_v, O\_v) := \{x \in \widehat{K} \mid x\_v \in O\_v\ \text{for all but finitely many $v$}\},$$ with basis of open sets $$\left\{ \prod\_{v\ \text{finite}} V\_v \mid V\_v \subseteq K\_v\ \text{open and $V\_v = O\_v$ for all but finitely many $v$}\right\}.$$
We will prove below that $\mathbb{A}\_{K, f}$ _is_ locally compact.

The _infinite adele ring_ is simply given as the (finite) direct product of the real/complex completions of $K$ at the real/complex places $$\mathbb{A}\_{K, \infty} := \prod_{v\ \text{infinite}} K\_v.$$

The _adele ring_ of $K$ is then given as the product of the infinite and finite adele rings: $$\mathbb{A}\_K := \mathbb{A}\_{K, \infty} \times \mathbb{A}\_{K, f}.$$

### Compactness of $O\_v$

Suppose now that $v$ is a finite place. A crucial result that will play a role later is that the $v$-adic ring of integers $O\_v$ is compact. It suffices to show that $O\_v$ is complete and totally bounded. For completeness, we show that it is _closed_, which can be proven in a similar way to the proof that it is open. Indeed, since the valuation is discrete, any open set is also closed. Since $O\_v$ is a closed set in a complete space, it is also complete. 

For $O\_v$ to be totally bounded means that for some fixed radius $\gamma$ > 0, we can cover $O\_v$ with finitely many open balls of radius $\gamma$. If $\gamma > 1$, then we can just take the open ball centred at zero and radius $\gamma$, as this contains $O\_v$. The discreteness of the $v$-adic valuation means that each $\gamma \le 1$ corresponds to some integer $\mu(\gamma)\ge 0$ in the sense that the ball of radius $\gamma$ is equal to the ball of radius $|\pi\_v|\_v^{\mu(\gamma)}$, where $\pi\_v$ generates $\mathfrak{m}\_v$. We note also that the residue field $O\_v/\mathfrak{m}\_v$, where $\mathfrak{m}\_v$ is the unique maximal ideal of $O\_v$, is finite. For any $n > 0$, $O\_v/(\mathfrak{m}\_v$^n)$ is therefore also finite as it can be viewed as $n$ copies of $O\_v/\mathfrak{m}\_v$. Hence, for a fixed $\gamma \le 1$, we take the finitely-many representatives from $O\_v/(\mathfrak{m}\_v^{\mu(n) + 1})$ and it can be checked that the balls centred at these representatives of radius $\gamma$ form a finite cover of $O\_v$. This completes the proof that $O\_v$ is compact.

### Local compactness of $K\_v$

Let $x \in K\_v$ and $N$ be a neighbourhood of $x$. Because any open set is closed, the maximal ideal $\mathfrak{m}\_v$ is closed and, since it is a closed subset of the compact space $O\_v$, it is also compact. Then $N$ contains a compact neighbourhood of $x$ because: we can always translate and shrink/inflate $\mathfrak{m}\_v$ so that it is inside $N$; the continuous image of an open compact set is also compact; and the image under translation and shrinking/inflating evidently remains open.

### Local compactness of $\mathbb{A}\_{K, f}$

The local compactness of the finite adele ring is difficult to show directly. Instead, we note that it suffices to cover $\mathbb{A}\_{K, f}$ with _open_ and _locally compact_ subsets. Then any neighbourhood of $x$ contains a compact neighbourhood by intersecting with the compact neighbourhood containing $x$ obtained from one of the locally compact subsets. To achieve this we use the finite $S$-adele ring $\mathbb{A}\_{S, K, f}$, where $S$ is some finite set of finite places, defined by $$\mathbb{A}\_{S, K, f} := \{x \in \widehat{K} \mid x\_v \in O\_v\ \text{for all $v \notin S$}\}.$$
This clearly belongs to the basis of open sets for $\mathbb{A}_{K, f}$, hence it is open. Moreover, through the map $x\mapsto ((x\_v)\_{v\in S}, (x\_v)\_{v\notin S})$, it is homeomorphic to $$\widehat{K}\_S := \prod\_{v \in S} K\_v \times \prod\_{v\notin S} O\_v,$$
which is locally compact as $\prod\_{v\in S} K\_v$ is a finite product of locally compact spaces and $\prod\_{v\notin S} O\_v$ is an infinite product of compact spaces.
Therefore $\mathbb{A}\_{S, K, f}$ is locally compact as well. Finally, the finite $S$-adele rings cover $\mathbb{A}\_{K, f}$ since $x \in \mathbb{A}\_{S(x), K, f}$, where $S(x)$ is the (finitely-many) places $v$ such that $x \notin O\_v$. 

### Local compactness of $\mathbb{A}\_{K, \infty}$

The infinite adele ring $\mathbb{A}\_{K, \infty}$ is locally compact because it is a finite product of the completions $K\_v$, where $v$ is an infinite place, each of which are locally compact.

### Local compactness of $\mathbb{A}\_{K}$

The adele ring is locally compact because it is the direct product of the infinite and finite adele rings, each of which have been shown to be locally compact.

## Overview of the code

The high-level code structure is modelled after the structure of Mathlib version [eaede86](https://github.com/leanprover-community/mathlib4/tree/eaede86aa7777630a3826cd8f3fbf0cbaafa53e6). In line with the above proof overview, we break down the specific location of results in the various files.

### Compactness of $O\_v$

The proofs that $O\_v$ is totally bounded, complete, and therefore compact can be found in [AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean).

- The result that $O\_v$ is compact is [here](https://github.com/smmercuri/adele-ring_locally-compact/blob/0e55b3c2fcf96b0fac2e7718ad2f1d66de9e22e0/AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean#L472).

### Local compactness of $K\_v$

- The result that $K\_v$ is locally compact for finite places $v$ is given in [AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean), specifically [here](https://github.com/smmercuri/adele-ring_locally-compact/blob/0e55b3c2fcf96b0fac2e7718ad2f1d66de9e22e0/AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean#L519).

### Local compactness of $\mathbb{A}\_{K, f}$

- The topology of the finite adele ring and other related definitions are found in [AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteAdeleRing.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteAdeleRing.lean).
- The definition of the finite $S$-adele ring and the proof that it is locally compact can be found in 
[AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean](https://github.com/smmercuri/adele-ring_locally-compact/blob/0e55b3c2fcf96b0fac2e7718ad2f1d66de9e22e0/AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean#L210) and [here](https://github.com/smmercuri/adele-ring_locally-compact/blob/0e55b3c2fcf96b0fac2e7718ad2f1d66de9e22e0/AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean#L421).
- The proof that the finite adele ring is locally compact can also be found in [AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean), specifically [here](https://github.com/smmercuri/adele-ring_locally-compact/blob/0e55b3c2fcf96b0fac2e7718ad2f1d66de9e22e0/AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean#L434).

### Local compactness of $\mathbb{A}\_{K, \infty}$

- The definition, topology and local compactness of the infinite adele ring are found in [AdeleRingLocallyCompact/RingTheory/DedekindDomain/InfiniteAdeleRing.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/InfiniteAdeleRing.lean).

### Local compactness of $\mathbb{A}\_{K}$

- The definition and local compactness of the adele ring are found in [AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdeleRing.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdeleRing.lean).

## Implementation notes

We collect some implementation notes and describe the Lean proof of the local compactness of the finite $S$-adele ring here.

- [AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean](AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean) currently contains some results that have been adapted from prior work (M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*) into Lean 4. One result remains unproven, which is the finiteness of the residue field of $O_v$. This also appears in (M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*). Once these results are available in Mathlib these will be updated accordingly.
- The finite $S$-adele ring is formalised as a subring of $\widehat{K}$, in an analogous way to the formalisation of $\mathbb{A}\_{K, f}$. It is given the subspace topology of $\mathbb{A}\_{K, f}$ by inducing along the open embedding $\mathbb{A}\_{S, K, f} \hookrightarrow \mathbb{A}\_{K, f}$. This is _the same_ as the topology obtained as a subtype of $\widehat{K}$.
- The equivalence and homeomorphism between $\widehat{K}$ and $\widehat{K}\_S$ are given, respectively, by Mathlib's `Equiv.piEquivPiSubtypeProd` and `Homeomorph.piEquivPiSubtypeProd`.
- The above homeomorphism then descends to a homeomorphism $\mathbb{A}\_{S, K, f}\cong \prod_{v\in S} K\_v \times \prod_{v\notin S} O\_v$, when the right-hand side is seen as a _subtype_ of $\widehat{K}\_S$.
- There is a homeomorphism between $\prod_{v\in S} K\_v \times \prod_{v\notin S} O\_v$ when viewed as a subtype of $\widehat{K}\_S$ vs. when it is defined as a topological space in its own right (i.e., with product topology). It is easy to show that the latter is locally compact using standard locally compact product results.
- This chain of homeomorphisms gives the proof of the local compactness of $\mathbb{A}\_{S, K, f}$. 
