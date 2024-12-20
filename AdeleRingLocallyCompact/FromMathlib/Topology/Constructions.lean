import Mathlib.Topology.Constructions
import AdeleRingLocallyCompact.FromMathlib.Logic.Function.Defs

protected theorem Continuous.piMap {Y π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [∀ i, TopologicalSpace (Y i)]
    {f : ∀ i, π i → Y i} (hf : ∀ i, Continuous (f i)) : Continuous (Pi.map f) :=
  continuous_pi fun i ↦ (hf i).comp (continuous_apply i)
