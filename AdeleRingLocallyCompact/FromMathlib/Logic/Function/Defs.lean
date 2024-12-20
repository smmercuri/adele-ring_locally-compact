import Mathlib.Logic.Function.Defs

def Pi.map {ι : Sort*} {α : ι → Sort*} {β : ι → Sort*} (f : (i : ι) → α i → β i) :
    ((i : ι) → α i) → (i : ι) → β i := fun a i => f i (a i)
