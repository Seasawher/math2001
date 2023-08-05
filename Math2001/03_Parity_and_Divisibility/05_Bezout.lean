/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.Ring
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  have h :=
    calc
      n = 16 * n - 3 * (5 * n) := by ring
      _ = 16 * n - 3 * (8 * a) := by rw [ha]
      _ = 8 * (2 * n - 3 * a) := by ring
  use 2 * n - 3 * a
  exact h

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  have h :=
    calc
      n = 2 * (3 * n) - 5 * n := by ring
      _ = 2 * (5 * a) - 5 * n := by rw [ha]
      _ = 5 * (2 * a - n) := by ring
  use 2 * a - n
  exact h

example {m : ℤ} (h2 : 5 ∣ m) (h1 : 8 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  have h :=
    calc
      n = 12 * n - 11 * n := by ring
      _ = 12 * n - 6 * a := by rw [ha]
      _ = 6 * (2 * n - a) := by ring
  use 2 * n - a
  exact h

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  sorry

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨ a, ha ⟩ := h1 
  obtain ⟨ b, hb ⟩ := h2
  have h :=
    calc
      n = 36 * n - 35 * n := by ring
      _ = 36 * (7 * a) - 35 * n := by rw [ha]
      _ = 36 * (7 * a) - 35 * (9 * b) := by rw [hb]
      _ = 63 * (4 * a - 5 * b) := by ring
  use 4 * a - 5 * b
  exact h

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  sorry
