# Local Compactness of the Adele Ring of a Number Field

This repository contains the source code for the paper "Formalising the local compactness of the adele ring".
This code requires Lean 4.7.0 and uses mathlib's version [eaede86](https://github.com/leanprover-community/mathlib4/tree/eaede86aa7777630a3826cd8f3fbf0cbaafa53e6).

The adele ring of a number field is a central object in modern number theory and its status as a locally compact topological ring is one of the key reasons why, leading to its widespread use within the Langlands Program. 
In this repository, we build upon [the work](https://drops.dagstuhl.de/storage/00lipics/lipics-vol237-itp2022/LIPIcs.ITP.2022.14/LIPIcs.ITP.2022.14.pdf) of Maria Inés de Frutos-Fernández who first formalised the adele ring of global fields in Lean, much of which has been subsequently integrated into mathlib.
The main result within this code is the proof that the adele ring of a number field is locally compact.
Along the way, we formalise Archimedean completion of a number field using recent advances in mathlib, and use this to re-formalise the infinite adele ring as the finite product of all such completions.
We also formalise the local compactness of all completions of a number field, the compactness of the ring of integers of non-Archimedean completions of a number field, and the finite $S$-adele ring, all of which are important tools for proving the local compactness of the adele ring.

We also port some foundational results on discrete valuations from more [recent work](https://github.com/mariainesdff/local_fields_journal/tree/0b408ff3af36e18f991f9d4cb87be3603cfc3fc3) by Maria Inés de Frutos-Fernández and Filippo A. E. Nuccio.
In particular we have an outstanding `sorry` in our result which follows immediately from that code.

## Documentation

The documentation for this project can be found [here](https://smmercuri.github.io/adele-ring_locally-compact/).
This contains the documentation for all the code contained in this branch, as well as the versions of mathlib and Lean that the project uses.

The latest documentation for Lean and its various libraries can be found [here](https://leanprover-community.github.io/mathlib4_docs/).

## Overview of the code

The code for various sections of the paper can be found as follows.

### Section 2
- Section 2.3: The result that the pullback under a field embedding of a completable topological field is a completable topological field is in [UniformSpace/Basic.lean](./AdeleRingLocallyCompact/Topology/UniformSpace/Basic.lean).

### Section 3
- Section 3.1.2: The completion of a number field at an infinite place is in [Embeddings.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/Embeddings.lean).
- Section 3.1.3: The formalisation of the infinite adele ring is in [InfiniteAdeleRing.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/InfiniteAdeleRing.lean).
- Section 3.2.2: Topological results for the finite adele ring are in [FiniteAdeleRing.lean](./AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteAdeleRing.lean).
- Section 3.3: The formalisation of the adele ring is in [AdeleRing.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/AdeleRing.lean).

### Section 4
- Section 4.1: The proof that each Archimedean completion of a number field is locally compact is in [Embeddings.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/Embeddings.lean) and that the infinite adele ring is locally compact is in [InfiniteAdeleRing.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/InfiniteAdeleRing.lean).
- Section 4.2.1: Compactness results for non-Archimedean completions of a number field are found in [AdicValuation.lean](./AdeleRingLocallyCompact/RingTheory/DedekindDomain/AdicValuation.lean). 
- Section 4.2.2: The proof that the finite $S$-adele ring is locally compact is in [FiniteSAdeleRing.lean](./AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean).
- Section 4.2.3: The proof that the finite adele ring is locally compact is in [FiniteSAdeleRing.lean](./AdeleRingLocallyCompact/RingTheory/DedekindDomain/FiniteSAdeleRing.lean).
- Section 4.3: The proof that the adele ring is locally compact is in [AdeleRing.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/AdeleRing.lean).

### Section 5
- Section 5: The alternative approach for formalising the completion of a number field at an infinite place is in [EmbeddingsAlt.lean](./AdeleRingLocallyCompact/NumberTheory/NumberField/EmbeddingsAlt.lean).

## Installation instructions

This project requires Lean 4 and mathlib. To install Lean follow the instructions [here](https://leanprover-community.github.io/get_started.html).

After installation of Lean 4, this project can be installed by running `git clone https://github.com/smmercuri/adele-ring_locally-compact.git` from a terminal in the location you wish to place this project, and then `cd adele-ring_locally_compact`. This will install all branches and version history of the project. To obtain the version described in the paper and contained within this branch, follow up with the command `git checkout journal`. The project be installed by first running `source ~/.profile` (or `source ~/.bash_profile` depending on the OS) and then running `lake exe cache get`.

See [this page](https://leanprover-community.github.io/install/project.html) for further details on setting up Lean projects.
