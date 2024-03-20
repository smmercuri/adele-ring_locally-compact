# FiniteSAdeleRing.lean Inventory

This file currently contains results about the finite S-adele ring.

The main results of this file involve homeomorphisms across several topological spaces. The point of these results are to allow us to show that the finite S-adele ring is locally compact. Usually, this is given by the argument that $\mathbb{A}_{S, K, f}$ is _the same_ as $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$, which is locally compact as $\prod_{v\in S} K_v$ is a finite product of locally compact spaces and $ \prod_{v\notin S} O_v$ is an infinite product of compact spaces. But actually "_the same_" is given by a number of equivalences leading to the result as follows.

- First we define $\mathbb{A}_{S, K, f}$ as a subring of $\prod_v K_v$, in an analogous way to the formalisation of $\mathbb{A}_{K, f}$. We could have alternatively defined it as a subring of $\mathbb{A}_{K, f}$, however we chose not to as $\mathbb{A}_{K, f}$ is also the direct limit of the $\mathbb{A}_{S, K, f}$ so future work may benefit from these two objects having the same-level type.
- Next we give $\mathbb{A}_{S, K, f}$ the subspace topology of $\mathbb{A}_{K, f}$. Since we did not define it as a subring of $\mathbb{A}_{K, f}$, this is achieved by defining an embedding $\mathbb{A}_{S, K, f} \hookrightarrow \mathbb{A}_{K, f}$ and inducing along this. 
- It turns out that the topology of $\mathbb{A}_{S, K, f}$ viewed as a subsapce of $\mathbb{A}_{K, f}$ is _the same_ as the product topology it gets when viewed as a subspace of $\prod_v K_v$, which is crucial and we prove it here.
- On the other hand, $\prod_{v\in S} K_v \times \prod_{v\notin S} K_v$ is usually seen as mathematically equal to $\prod_v K_v$, but of course they are not definitionally, and in Lean this kind of non-definitional equivalence of types is already given in Mathlib. We show additionally that they are homeomorphic.
- We can define $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ as a subtype of $\prod_{v\in S} K_v \times \prod_{v\notin S} K_v$ and give it the subspace topology. 
- The homeomorphism proven earlier of $\prod_v K_v \cong \prod_{v\in S} K_v \times \prod_{v\notin S} K_v$ now descends to a homeomorphism on subtypes $\mathbb{A}_{S, K, f}\cong \prod_{v\in S} K_v \times \prod_{v\notin S} O_v$. Thus $\mathbb{A}_{S, K, f}$ is locally compact provided $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ is.
- The final piece of the puzzle, which may not be required actually, is a homeomorphism between $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ when seen as a subtype of $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ vs. when viewed as a topological space on it's own right. The former is `SProdAdicCompletionIntegers'` and the latter is `SProdAdicCompletionIntegers`. This is because it seems much easier to prove local compactness of the non-prime version, but the non-prime version does not obtain an easy homeomorphic descent to $\mathbb{A}_{S, K, f}$ as shown above for the prime version. Maybe I can try to prove the prime version is locally compact by some subspace argument....

### Definitions

- `SProdAdicCompletions`: $\prod_{v \in S} K_v \times \prod_{v\notin S} K_v$ 
- `SProdAdicCompletionIntegers`: $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v$
- `SProdAdicCompletionIntegers.piSubtypeProd`: $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v \to \prod_v K_v$
- `FiniteSAdeleRing.IsFiniteSAdele`: $\prod_v K_v \to \texttt{Prop}; x \mapsto \forall v\notin S, x_v \in O_v$
- `FiniteSAdeleRing.finiteSAdeleRing`: Ring $\mathbb{A}_{S, K, f}$ with carrier $\{x \mid IsFiniteSAdele x\}$.
- `FiniteSAdeleRing.embedding`: $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$
- `FiniteSAdeleRing.projection`: $\mathbb{A}_{S, K, f} \to K_w$
- `FiniteSAdeleRing.generatingSet`: $\{\texttt{embedding}^{-1}(U) \mid U \in \texttt{FiniteAdeleRing.generatingSet}\}$
- `FiniteSAdeleRing.SProdAdicCompletionIntegers'`: Subtype of $\prod_{v \in S} K_v \times \prod_{v\notin S} K_v$ corresponding to $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v$. This is obviously, but not definitionally, equivalent to the non-prime version.

### Instances

- `SProdAdicCompletions.Coe` : $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v \to \prod_{v \in S} K_v \times \prod_{v\notin S} K_v$
- `SProdAdicCompletions.TopologicalSpace`: $\prod_{v \in S} K_v \times \prod_{v\notin S} K_v$ is given the product topology.
- `SProdAdicCompletions.CommRing`: $\prod_{v \in S} K_v \times \prod_{v\notin S} K_v$ is a commutative ring.
- `SProdAdicCompletions.Inhabited`: $\prod_{v \in S} K_v \times \prod_{v\notin S} K_v$ is inhabited.
- `SProdAdicCompletionIntegers.topologicalSpace`: $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v$ is given the product topology.
- `SProdAdicCompletionIntegers.CommRing`: $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v$ is a commutative ring.
- `SProdAdicCompletionIntegers.Inhabited`: $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v$ is inhabited.
- `FiniteSAdeleRing.inst : TopologicalSpace (SProdAdicCompletionIntegers')`: is given the subspace topology of $\prod_{v \in S} K_v \times \prod_{v\notin S} K_v$

### Theorems

- `SProdAdicCompletions.coe_injective`: The coercion $\prod_{v \in S} K_v \times \prod_{v\notin S} O_v \to \prod_{v \in S} K_v \times \prod_{v\notin S} K_v$ is injective.
- `SProdAdicCompletions.homeomorph_piSubtypeProd`: The top-level homeomorphism $\prod_v K_v\cong \prod_{v\in S} K_v \times \prod_{v\notin S} K_v$.
- `SProdAdicCompletionIntegers.equiv_invProp`: if $x \in \prod_{v\in S} K_v \times \prod_{v\in S} O_v$ viewed as a type, then `Subtype.val` of $x_{2, v}$ is in $O_v$ (not sure if this is needed?)
- `SProdAdicCompletionIntegers.equiv`: The type equivalence between $\prod_{v\in S} K_v \times \prod_{v\in S} O_v$ viewed in two different ways.
- `SProdAdicCompletionIntegers.homeomorph` : The homeomorphism between $\prod_{v\in S} K_v \times \prod_{v\in S} O_v$ viewed in two different ways.
- `FiniteSAdeleRing.mul`: Multiplicative ring axiom.
- `FiniteSAdeleRing.one`: One element ring axiom. 
- `FiniteSAdeleRing.add`: Additive ring axiom. 
- `FiniteSAdeleRing.zero`: Zero element ring axiom. 
- `FiniteSAdeleRing.neg`: Negation ring axiom.
- `FiniteSAdeleRing.mem_isFiniteAdele`: A finite S-adele is a finite adele.
- `FiniteSAdeleRing.isFiniteSAdele_inclusion`: If $x\in S$, then the inclusion $\iota_v(x)$ of $x \in K_v$ in $\mathbb{A}_{K, f}$ is a finite S-adele.
- `FiniteSAdeleRing.isFiniteSAdele_inclusion`: The inclusion $\iota_v(x)$ of $x \in O_v$ in $\mathbb{A}_{K, f}$ is a finite S-adele.
- `FiniteSAdeleRing.projection_range`: The image of the projection $\pi_v$ of the set of S-adeles inside $\mathbb{A}_{K, f}$ is $K_v$ if $v\in S$ else $O_v$.
- `FiniteSAdeleRing.embeddingInducing`: The map $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$ is inducing.
- `FiniteSAdeleRing.embeddingInjective`: The map $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$ is injective.
- `FiniteSAdeleRing.embeddingRange`: The image of $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$ coincides with the finite adeles that are finite S-adeles.
- `FiniteSAdeleRing.embedding_range`: DUPLICATE of above with a better proof (but worse name?).
- `FiniteSAdeleRing.embeddingRange_eq_pi`: The image of $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$ is $\prod_v X_v$, where $X_v = K_v$ if $v \in S$ else $O_v.
- `FiniteSAdeleRing.embeddingOpen`: The map $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$ is an open embedding.
- `FiniteSAdeleRing.isFiniteSAdele_piSubtypeProd`: If $x \in \prod_{v\in S} K_v \times \prod_{v\notin S} O_v$ then it is an S-adele when viewed as an element of $\prod_v K_v$.
- `FiniteSAdeleRing.finiteSAdeleEquiv`: The type equivalence between $\mathbb{A}_{S, K, f}$ and $\prod_{v\in S} K_v \times \prod_{v\notin S} O_v$.
- `FiniteSAdeleRing.generateFrom`: The induced/subspace topology of $\mathbb{A}_{S, K, f}$ is generated by the generating set defined in `FiniteSAdeleRing.generatingSet`. NOTE: do we need this?
- `FiniteSAdeleRing.embeddingRange_mem_generatingSet`: The image of the embedding $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$ is in the generating set of $\mathbb{A}_{K, f}$.
- `FiniteSAdeleRing.set_univ_mem_generatingSet`: The entirety of $\mathbb{A}_{S, K, f}$ is in its generating set.
- `FiniteSAdeleRing.mem_finiteAdeleRingGeneratingSet_range_inter`: Given some generating open set V of $\mathbb{A}_{K, f}$, then its intersection with finite S-adeles is a generating open set of $\mathbb{A}_{S, K, f}$.
- `FiniteSAdeleRing.subtype_val_embedding`: The `Subtype.val` map from $\mathbb{A}_{S, K, f}$ to $\prod_v K_v$ factors through the embedding $\mathbb{A}_{S, K, f} \to \mathbb{A}_{K, f}$.
- `FiniteSAdeleRing.subtype_val_range_eq_pi`: The image of $\mathbb{A}_{S, K, f}\to \prod_v K_v$ is $\prod_v X_v$, where $X_v = K_v$ if $v \in S$ else $O_v.
- `FiniteSAdeleRing.generatingSet_eq`: Explicit characterisation of the generating set of $\mathbb{A}_{S, K, f}$ of the form expected by the infinite product topology. This is the main result that allows us to identify the two sources of topologies on $\mathbb{A}_{S, K, f}$ as the same.
- `FiniteSAdeleRing.topologicalSpace_eq_piTopologicalSpace`: The two sources of topologies on $\mathbb{A}_{S, K, f}$ coincide (subspace topology of $\mathbb{A}_{K, f}$ equals the subspace topology of $\prod_v K_v$).
- `FiniteSAdeleRing.homeomorph_piSubtypeProd`: The descended homeomorphism between $\mathbb{A}_{S, K, f}$ and $\prod_{v\in S} K_v \times \prod_{v\in S} O_v$, where the latter is thought of as a subtype of $\prod_v K_v$.