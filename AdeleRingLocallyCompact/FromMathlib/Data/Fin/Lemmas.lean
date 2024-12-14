import Init.Data.Fin.Lemmas

@[simp]
theorem last_zero : (Fin.last 0 : Fin 1) = 0 := by
  ext
  simp

@[simp]
theorem Fin.zero_eq_last_iff {n : Nat} : (0 : Fin (n + 1)) = Fin.last n ↔ n = 0 := by
  constructor
  · intro h
    simp_all [Fin.ext_iff]
  · intro h
    rw [h]
    simp

@[simp]
theorem Fin.last_eq_zero_iff {n : Nat} : Fin.last n = 0 ↔ n = 0 := by
  simp [eq_comm (a := Fin.last n)]
