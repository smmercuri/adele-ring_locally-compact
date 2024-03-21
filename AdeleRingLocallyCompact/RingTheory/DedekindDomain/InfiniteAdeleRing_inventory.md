# FiniteAdeleRing.lean Inventory

This file currently contains results about the finite adele ring.

The main results of this file involve defining the topological space for finite adele ring (adapted from previous work of Maria Ines). 

### Definitions

- `DedekindDomain.infiniteAdeleRing`: $\mathbb{A}_{K, \infty} := \mathbb{R} \otimes_{\mathbb{Q}} K$
- `InfiniteAdeleRing.RatBasis.equiv`: The linear equivalence between $\mathbb{Q}^{\text{dim}_{\mathbb{Q}}(K)}$ and $K$.
- `InfiniteAdeleRing.RatBasis.to_tensorBasis_funLike`: Given a basis $B_i$ of $\mathbb{Q}^n$, gives the corresponding basis $1 \otimes B_i$ of $\mathbb{R}\otimes_{\mathbb{Q}} \mathbb{Q}^n$ as a `FunLike`.
- `InfiniteAdeleRing.RealBasis.funLike`: Gives the explicit `FunLike` instance of a basis $C_i$ of $\mathbb{R}^n$.
- `InfiniteAdeleRing.real_tensorProduct_rat_toFun`: The linear map $\mathbb{R} \otimes_{\mathbb{Q}} \mathbb{Q}^n \to \mathbb{R}^n$ which sends $1 \otimes B_i\mapsto C_i$.
- `InfiniteAdeleRing.real_tensorProduct_rat_invFun`: The linear map $\mathbb{R}^n \to \mathbb{R} \otimes_{\mathbb{Q}} \mathbb{Q}^n$ which sends $C_i \mapsto 1 \otimes B_i$.
- `InfiniteAdeleRing.real_tensorProduct_numberField_toFun`: The linear map $\mathbb{A}_{K, \infty}\to \mathbb{R}^{\text{dim}_{\mathbb{Q}}(K)}$.
- `InfiniteAdeleRing.real_tensorProduct_numberField_invFun`: The linear map $\mathbb{R}^{\text{dim}_{\mathbb{Q}}(K)} \to \mathbb{A}_{K, \infty}$.

### Instances

- `InfiniteAdeleRing.instRing` : $\mathbb{R}^n$ is a ring.
- `InfiniteAdeleRing.piReal_topologicalSpace`: $\mathbb{R}^n$ is given the product topology.
- `InfiniteAdeleRing.instTopologicalRing`: $\mathbb{R}^n$ is a topological ring.
- `InfiniteAdeleRing.topologicalSpace`: $\mathbb{A}_{K, \infty}$ is given the topology induced by the equivalence with $\mathbb{R}^{\text{dim}_{\mathbb{Q}}(K)}$.

### Theorems

- `InfiniteAdeleRing.real_tensorProduct_rat_equiv`: The linear equivalence $\mathbb{R} \otimes_{\mathbb{Q}}\mathbb{Q}^n \cong \mathbb{R}^n$.
- `InfiniteAdeleRing.real_tensorProduct_numberField_equiv`: The linear equivalence $\mathbb{A}_{K, \infty} \cong \mathbb{R}^{\text{dim}_{\mathbb{Q}}(K)}$.

## Namespace structure

- `DedekindDomain`
    - `InfiniteAdeleRing`
