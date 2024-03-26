# Local Compactness of the Adele Ring

## AdicValuation.lean

This file contains results about the $v$-adic completion $K_v$ of the fraction field $K$ of a Dedekind domain $R$ of Krull dimension $1$ and its ring of integers $O_v$. The main results are the local compactness of $K_v$ and the compactness of $O_v$. This file contains mainly results that have been adapted from prior work (M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*) into Lean 4. One result remains unproven, which is the finiteness of the residue field of $O_v$. This also appears in (M.I. de Frutos-Fernández, F.A.E. Nuccio, *A Formalization of Complete Discrete Valuation Rings and Local Fields*), but porting of that particular result is left for future work.

## FiniteAdeleRing.lean

This file currently contains results about the finite adele ring. We adapt prior work (M.I. de Frutos-Fernàndez, *Formalizing the Ring of Adèles of a Global Field*) to define the topology of 
the finite adele ring in Lean 4.

## FiniteSAdeleRing.lean 

This file currently mostly contains results about the finite S-adele ring $\mathbb{A}_{S, K, f}$. This file contains the local compactness of the finite S-adele ring and the finite adele ring. Local compactness of the finite S-adele ring is achieved by establishing homeomorphisms across several topological spaces. The point of these homeomorphisms is to establish a homeomorphism between  $\mathbb{A}_{S, K, f}$ and $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$, which is locally compact as $\prod_{v\in S} K_v$ is a finite product of locally compact spaces and $ \prod_{v\notin S} O_v$ is an infinite product of compact spaces. Local compactness of the finite adele ring is then obtained since the finite S-adeles provide a locally compact and open covering of the finite adele ring.

- First we define $\mathbb{A}_{S, K, f}$ as a subring of $\prod_v K_v$, in an analogous way to the formalisation of $\mathbb{A}_{K, f}$. We could have alternatively defined it as a subring of $\mathbb{A}_{K, f}$, however we chose not to as $\mathbb{A}_{K, f}$ is also the direct limit of the $\mathbb{A}_{S, K, f}$ so future work may benefit from these two objects having the same-level type.
- Next we give $\mathbb{A}_{S, K, f}$ the subspace topology of $\mathbb{A}_{K, f}$. Since we did not define it as a subring of $\mathbb{A}_{K, f}$, this is achieved by defining an embedding $\mathbb{A}_{S, K, f} \hookrightarrow \mathbb{A}_{K, f}$ and inducing along this. 
- It turns out that the topology of $\mathbb{A}_{S, K, f}$ viewed as a subsapce of $\mathbb{A}_{K, f}$ is _the same_ as the product topology it gets when viewed as a subspace of $\prod_v K_v$, which is crucial and we prove it here.
- On the other hand, $\prod_{v\in S} K_v \times \prod_{v\notin S} K_v$ is usually seen as mathematically equal to $\prod_v K_v$, but of course they are not definitionally, and in Lean this kind of non-definitional equivalence of types is already given in Mathlib. We show additionally that they are homeomorphic.
- We can define $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ as a subtype of $\prod_{v\in S} K_v \times \prod_{v\notin S} K_v$ and give it the subspace topology. 
- The homeomorphism proven earlier of $\prod_v K_v \cong \prod_{v\in S} K_v \times \prod_{v\notin S} K_v$ now descends to a homeomorphism on subtypes $\mathbb{A}_{S, K, f}\cong \prod_{v\in S} K_v \times \prod_{v\notin S} O_v$. Thus $\mathbb{A}_{S, K, f}$ is locally compact provided $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ is.
- The final piece is a homeomorphism between $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ when seen as a subtype of $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ vs. when viewed as a topological space on it's own right. The former is `SProdAdicCompletionIntegers'` and the latter is `SProdAdicCompletionIntegers`. This is because it seems much easier to prove local compactness of the non-prime version, but the non-prime version does not obtain an easy homeomorphic descent to $\mathbb{A}_{S, K, f}$ as shown above for the prime version. 

## InfiniteAdeleRing.lean

This file contains results about the infinite adele ring. We define its topology and show that it is locally compact.

## AdeleRing.lean 

The main results of this file involve the definition of the adele ring as the direct product of the infinite adele ring and the finite adele ring, and we endow it with a topological space. This then inherits local compactness from the previously established local compactness of the infinite adele ring and finite adele ring.
