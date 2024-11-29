# Local Compactness of the Adele Ring of a Number Field

This repository contains the proof that the adele ring of a number field is locally compact, formalised in Lean 4.10.0 using Mathlib's version [caac5b1](https://github.com/leanprover-community/mathlib4/tree/caac5b13fb72ba0c5d0b35a0067de108db65e964).

That the adele ring of a number field is locally compact is one of the motivators for defining the adele ring using the _restricted_ direct product over all completions, rather than just the usual direct product. 
Moreover, this allows one to do harmonic analysis over the subgroup of units of the adele ring which was done in Tate's landmark thesis, a precursor to the Langlands program. 

This work follows on from prior work of Maria Inés de Frutos-Fernández, who first formalised the definition of the adele ring of a global field [here](https://github.com/mariainesdff/ideles/tree/journal-submission), some of which has been ported to Mathlib's version [eaede86](https://github.com/leanprover-community/mathlib4/tree/eaede86aa7777630a3826cd8f3fbf0cbaafa53e6), and we also use some results from their recent work with Filippo A. E. Nuccio [here](https://github.com/mariainesdff/local_fields_journal/tree/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3), namely we port some foundational results on discrete valuations.

## Overview of the proof

### Introduction

Let $K$ be an algebraic number field over $\mathbb{Q}$ and let $O\_K$ be its ring of integers, which is a Dedekind domain of Krull dimension $1$. 
By the extension of Ostrowski's theorem to number fields any valuation on $K$ is equivalent to some $\mathfrak{p}$-adic valuation on $K$ or an absolute value arising from the real and complex embeddings of $K$. 
Equivalence classes of valuations on $K$ are known as _places_. 
Thus places of $K$ are indexed by the real/complex embeddings of $K$ and by the primes $\mathfrak{p}$ of $O\_K$; the former are called the _infinite_ places and the latter the _finite_ places. 

Let $v$ be a place of $K$, then we denote by $K\_v$ the completion of $K$ with respect to some representative valuation of the place $v$. 
The place $v$ extends naturally to a place on $K\_v$, which we denote by $|\cdot|\_v$. 
The integral closure of $O\_K$ inside $K\_v$ is called the ($v$-adic) ring of integers and is denoted $\mathcal{O}\_v$; this corresponds to the ring of all $x \in K\_v$ such that $|x|_v \le 1$. 

The direct product of completions of $K$ at finite places is denoted 

$$\widehat{K} := \prod\_{v\ \text{finite}} K\_v.$$ 

This product is _not_ locally compact, given the product topology. 
On the other hand, we define the _finite adele ring_ as the _restricted_ direct product 

$$\mathbb{A}\_{K, f} = \prod\_{v\ \text{finite}}(K\_v, \mathcal{O}\_v) := \\{x \in \widehat{K} \mid x\_v \in \mathcal{O}\_v\ \text{for all but finitely many}\ v\\},$$ 

with basis of open sets 

$$\left\\{ \prod\_{v\ \text{finite}} V\_v \mathrel{\bigg|} V\_v \subseteq K\_v\ \text{open and}\ V\_v = \mathcal{O}\_v\ \text{for all but finitely many}\ v\right\\}.$$

We will prove below that $\mathbb{A}\_{K, f}$ _is_ locally compact.

The _infinite adele ring_ is given as the (finite) direct product of the real/complex completions of $K$ at the real/complex places 

$$\mathbb{A}\_{K, \infty} := \prod_{v\ \text{infinite}} K\_v.$$

The _adele ring_ of $K$ is then given as the product of the infinite and finite adele rings: 

$$\mathbb{A}\_K := \mathbb{A}\_{K, \infty} \times \mathbb{A}\_{K, f}.$$

### Compactness of $\mathcal{O}\_v$

Suppose now that $v$ is a finite place. 
A crucial result that will play a role later is that the $v$-adic ring of integers $\mathcal{O}\_v$ is compact. 
It suffices to show that $\mathcal{O}\_v$ is complete and totally bounded. For completeness, we show that it is _closed_, which can be proven in a similar way to the proof that it is open. 
Indeed, since the valuation is discrete, any open set is also closed. 
Since $\mathcal{O}\_v$ is a closed set in a complete space, it is also complete. 

For $\mathcal{O}\_v$ to be totally bounded means that for some fixed radius $\gamma$ > 0, we can cover $\mathcal{O}\_v$ with finitely many open balls of radius $\gamma$. 
It suffices to check this for $\gamma \le 1$. 
Each such $\gamma$ corresponds to some integer $\mu(\gamma)\ge 0$ in the sense that the ball of radius $\gamma$ is equal to the ball of radius $|\pi\_v|\_v^{\mu(\gamma)}$, where $\pi\_v$ generates the unique maximal ideal $\mathfrak{m}\_v$ of $\mathcal{O}\_v$. 
We note also that the residue field $\mathcal{O}\_v/\mathfrak{m}\_v$ is finite. 
For any $n > 0$, $\mathcal{O}\_v/(\mathfrak{m}\_v^n)$ is therefore also finite as it can be viewed as $n$ copies of $\mathcal{O}\_v/\mathfrak{m}\_v$. 
Hence, for a fixed $\gamma \le 1$, we take the finitely-many representatives from $\mathcal{O}\_v/(\mathfrak{m}\_v^{\mu(n) + 1})$ and it can be checked that the balls centred at these representatives of radius $\gamma$ form a finite cover of $\mathcal{O}\_v$. 
This completes the proof that $\mathcal{O}\_v$ is compact.

### Local compactness of $K\_v$

It is enough to show that $0$ has a compact neighbourhood, because we can translate and dilate/shrink this neighbourhood to be contained in a neighbourhood of any other point.
The maximal ideal $\mathfrak{m}\_v$ is a clopen subset of the compact space $\mathcal{O}\_v$, so it is a compact neighbourhood of $0$.

### Local compactness of $\mathbb{A}\_{K, f}$

The local compactness of the finite adele ring is difficult to show directly. 
Instead, we note that it suffices to cover $\mathbb{A}\_{K, f}$ with _open_ and _locally compact_ subsets. 
Then any neighbourhood of $x$ contains a compact neighbourhood by intersecting with the compact neighbourhood containing $x$ obtained from one of the locally compact subsets. 
To achieve this we use the finite $S$-adele ring $\mathbb{A}\_{S, K, f}$, where $S$ is some finite set of finite places, defined by 

$$\mathbb{A}\_{S, K, f} := \\{x \in \widehat{K} \mid x\_v \in \mathcal{O}\_v\ \text{for all}\ v \notin S\\}.$$

This clearly belongs to the basis of open sets for $\mathbb{A}_{K, f}$, hence it is open. Moreover, through the map $x\mapsto ((x\_v)\_{v\in S}, (x\_v)\_{v\notin S})$, it is homeomorphic to 

$$\widehat{K}\_S := \prod\_{v \in S} K\_v \times \prod\_{v\notin S} \mathcal{O}\_v,$$

which is locally compact as $\prod\_{v\in S} K\_v$ is a finite product of locally compact spaces and $\prod\_{v\notin S} \mathcal{O}\_v$ is an infinite product of compact spaces.
Therefore $\mathbb{A}\_{S, K, f}$ is locally compact as well. Finally, the finite $S$-adele rings cover $\mathbb{A}\_{K, f}$ since $x \in \mathbb{A}\_{S(x), K, f}$, where $S(x)$ is the (finitely-many) places $v$ such that $x \notin \mathcal{O}\_v$. 

### Local compactness of $\mathbb{A}\_{K, \infty}$

The infinite adele ring $\mathbb{A}\_{K, \infty}$ is locally compact because it is a finite product of the completions $K\_v$, where $v$ is an infinite place, each of which are locally compact.

### Local compactness of $\mathbb{A}\_{K}$

The adele ring is locally compact because it is the direct product of the infinite and finite adele rings, each of which have been shown to be locally compact.

## Overview of the code

The high-level code structure is modelled after the structure of Mathlib version [caac5b1](https://github.com/leanprover-community/mathlib4/tree/caac5b13fb72ba0c5d0b35a0067de108db65e964). In line with the above proof overview, we break down the specific location of results in the various files.

### Compactness of $\mathcal{O}\_v$

The proofs that $\mathcal{O}\_v$ is totally bounded, complete, and therefore compact can be found in [`RingTheory.DedekindDomain.AdicValuation`](AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean).

### Local compactness of $K\_v$

- The result that $K\_v$ is locally compact for finite places $v$ is given in [`RingTheory.DedekindDomain.AdicValuation`](AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean).

### Local compactness of $\mathbb{A}\_{K, f}$

- Some helper results for the finite adele ring are found in [`RingTheory.DedekindDomain.FiniteAdeleRing`](AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteAdeleRing.lean).
- The definition of the finite $S$-adele ring and the proof that it is locally compact can be found in 
[`RingTheory.DedekindDomain.FinsetAdeleRing`](AdeleRingLocallyCompact/RingTheory/DedekindDomain/FinsetAdeleRing.lean).
- The proof that the finite adele ring is locally compact can also be found in [`RingTheory.DedekindDomain.FinsetAdeleRing`](AdeleRingLocallyCompact/RingTheory/DedekindDomain/FinsetAdeleRing.lean).

### Local compactness of $\mathbb{A}\_{K, \infty}$

- The completion of a number field at the infinite places and its local compactness is formalised in [`NumberTheory.NumberField.Completion`](AdeleRingLocallyCompact/NumberTheory/NumberField/Completion.lean).
- The definition and local compactness of the infinite adele ring are found in [`NumberTheory.NumberField.InfiniteAdeleRing`](AdeleRingLocallyCompact/NumberTheory/NumberField/InfiniteAdeleRing.lean).

### Local compactness of $\mathbb{A}\_{K}$

- The definition and local compactness of the adele ring are found in [`NumberTheory.NumberField.AdeleRing`](AdeleRingLocallyCompact/NumberTheory/NumberField/AdeleRing.lean).

## Implementation notes

We collect some implementation notes and describe the Lean proof of the local compactness of the finite $S$-adele ring here.

- [`FromLocalClassFieldTheory.LocalClassFieldTheory`](AdeleRingLocallyCompact/FromLocalClassFieldTheory/LocalClassFieldTheory.lean) currently contains some results that have been adapted from prior work (M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*) into Lean 4. One result remains unproven in our work is the finiteness of the residue field of $O_v$. This also appears in (M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*). 
- The finite $S$-adele ring is formalised as a subtype of $\widehat{K}$, in an analogous way to the formalisation of $\mathbb{A}\_{K, f}$. 
This gets the subspace topology of $\widehat{K}$.
- The equivalence and homeomorphism between $\widehat{K}$ and $\widehat{K}\_S$ are given, respectively, by Mathlib's `Equiv.piEquivPiSubtypeProd` and `Homeomorph.piEquivPiSubtypeProd`.
This homeomorphism then descends to a homeomorphism $\mathbb{A}\_{S, K, f}\cong \prod_{v\in S} K\_v \times \prod_{v\notin S} \mathcal{O}\_v$, when the right-hand side is seen as a _subtype_ of $\widehat{K}\_S$.
- There is a homeomorphism between $\prod_{v\in S} K\_v \times \prod_{v\notin S} \mathcal{O}\_v$ when viewed as a subtype of $\widehat{K}\_S$ vs. when it is defined as a topological space in its own right (i.e., with product topology). 
It is easy to show that the latter is locally compact using standard locally compact product results.
- This chain of homeomorphisms gives the proof of the local compactness of $\mathbb{A}\_{S, K, f}$. 
- Lean always expects a single instance of a class on a type. 
A number field, however, has multiple distinct uniform structures coming from infinite places. 
To handle this ambiguity, we use a dependent type synonym `WithAbs`, which simply renames a semiring and makes it depend on absolute values.
When `v` is an infinite place on `K`, we can instead view `K` as `WithAbs v.1`.
This allows the type class inference system to automatically infer any assigned instances that depend on absolute values.

## TODOs
- Incorporate the proof that `v.adicCompletionIntegers K` has finite residue field.
- v2.0 : Show that $K$ is a discrete and cocompact subgroup of the additive group of $\mathbb{A}\_K$.
    - Define the adelic norm.
    - Prove the product formula for global adeles: if $x \in K \subseteq \mathbb{A}\_K$ then $\|x\| = 1$.
    - This is enough to show that $K$ is a discrete subgroup.
    - Prove base change for adele rings : if $K/L$ then $\mathbb{A}\_L = \mathbb{A}\_K\otimes\_K L$.
    - Helper result: for all finite places $v$, if $y \in K\_v$ then there exists $x \in K$ such that $\|y - x\|\_v\le 1$ and $\|x\|\_w \le 1$ for all $w \ne v$.
    - This is enough to show that $\mathbb{A}\_{\mathbb{Q}}/\mathbb{Q}$ is compact, since it's the continuous image of the compact set $\\{x \in \mathbb{A}\_{\mathbb{Q}}\mid \forall v, \|x\|\_v \le 1\\}$. Then use base change for general $K$.
- v3.0 : Show the idele group is locally compact. Probably requires refactoring the current code as follows.
    - Define `ProdAdicCompletions.IsRestrictedProduct (X : Subring (ProdAdicCompletions R K) (U : v \\to (Subring (v.adicCompletion K))))`
    - Refactor the current proof of local compactness of adele ring to show that `ProdAdicCompletions.IsRestrictedProduct` is locally compact (requires the assumption that `U v` are all compact).
    - Then local compactness of finite adele ring follows immediateley with `U v = v.adicCompletionIntegers K`
    - Define idele ring as group of units with unit topology.
    - Show this is `IsRestrictedProduct` where `U v = (v.adicCompletionIntegers K)^*`, therefore locally compact.
