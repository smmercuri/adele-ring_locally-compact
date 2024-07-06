/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib
import AdeleRingLocallyCompact.NumberTheory.NumberField.Completion

/-!
# Infinite adele ring

This file formalises the definition of the infinite adele ring of a number field `K` as the
product of completions of `K` over its infinite places and we show that it is locally compact.
The definition of the completions are formalised in
[AdeleRingLocallyCompact.NumberTheory.NumberField.Embeddings](Embeddings.lean).

## Main definitions
 - `DedekindDomain.infiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its Archimedean places.

## Main results
 - `DedekindDomain.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
  locally compact space since it is a finite product of locally compact spaces.

## References
 * [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
infinite adele ring, number field
-/

noncomputable section

namespace NumberField

open InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
def infiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (infiniteAdeleRing K) := Pi.commRing

instance : Inhabited (infiniteAdeleRing K) := ⟨0⟩

instance : Nontrivial (infiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

end DerivedInstances

instance topologicalSpace : TopologicalSpace (infiniteAdeleRing K) := Pi.topologicalSpace

instance topologicalRing : TopologicalRing (infiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (infiniteAdeleRing K) := Pi.algebra _ _

/-- The global embedding of a number field into its infinite adele ring,
sending `x ∈ K` to `(x)ᵥ`. -/
abbrev globalEmbedding : K →+* infiniteAdeleRing K := algebraMap K (infiniteAdeleRing K)

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding K x v = (x : v.completion) := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (infiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

theorem RingEquiv.piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) (Y : ι → Type*)
    [(i : ι) → Mul (Y i)] [(i : ι) → Add (Y i)] [DecidablePred p] :
    ((i : ι) → Y i) ≃+* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) where
  toEquiv := Equiv.piEquivPiSubtypeProd p Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem RingEquiv.prodMap {R R' S S' : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [NonAssocSemiring R'] [NonAssocSemiring S'] (f : R ≃+* R') (g : S ≃+* S') :
    R × S ≃+* R' × S' where
  toEquiv := Equiv.prodCongr f g
  map_mul' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe, Prod_map, Prod.fst_mul,
      map_mul, Prod.snd_mul, Prod.mk_mul_mk]
  map_add' _ _ := by
    simp only [Equiv.toFun_as_coe, Equiv.prodCongr_apply, EquivLike.coe_coe, Prod_map, Prod.fst_add,
      map_add, Prod.snd_add, Prod.mk_add_mk]

-- TODO : add simp lemmas for these
theorem RingEquiv.piCongrLeft' {α β : Type*} (R : α → Type*)
    [(i : α) → NonUnitalNonAssocSemiring (R i)] (e : α ≃ β) :
    ((a : α) → R a) ≃+* ((b : β) → R (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' R e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem RingEquiv.piCongrLeft {α β : Type*} (R : β → Type*)
    [(i : β) → NonUnitalNonAssocSemiring (R i)] (e : α ≃ β) :
    ((a : α) → R (e a)) ≃+* ((b : β) → R b) := (RingEquiv.piCongrLeft' R e.symm).symm

instance : DecidablePred (IsReal : InfinitePlace K → Prop) := by
  intro v
  have : { v : InfinitePlace K | IsReal v }.Finite :=
    Set.Finite.subset (Set.univ_finite_iff_nonempty_fintype.2 ⟨inferInstance⟩) (Set.subset_univ _)
  exact decidable_of_iff (v ∈ this.toFinset) (by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq])

theorem equiv_mixedSpace :
    infiniteAdeleRing K ≃+*
      ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) := by
  have := (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
    (fun (v : InfinitePlace K) => v.completion))
  refine RingEquiv.trans this (RingEquiv.prodMap ?_ ?_)
  · exact RingEquiv.piCongrRight (fun ⟨v, hv⟩ => Completion.equivReal_of_isReal hv)
  · apply RingEquiv.trans <| RingEquiv.piCongrRight (fun v => Completion.equivComplex_of_isComplex
      ((not_isReal_iff_isComplex.1 v.2)))
    exact RingEquiv.piCongrLeft (fun _ => _) <|
      Equiv.subtypeEquivRight (fun v => not_isReal_iff_isComplex)

end InfiniteAdeleRing

end NumberField
