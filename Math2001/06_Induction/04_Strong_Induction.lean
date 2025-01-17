/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Extra
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
set_option push_neg.use_distrib true
set_option linter.unusedVariables false
open Nat


def F : ℕ → ℤ 
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n 

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by numbers
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by numbers
  | k + 2  =>
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
        _ = 2 ^ (k + 2) := by ring


namespace Nat

theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n 
  . -- case 1: `n` is prime
    use n
    constructor
    · apply hn
    · use 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn -- inductive hypothesis
    obtain ⟨p, hp, y, hy⟩ := IH
    use p
    constructor
    · apply hp
    · use x * y
      calc n = m * x := hx
        _ = (p * y) * x := by rw [hy]
        _ = p * (x * y) := by ring

/-! # Exercises -/

lemma le_imp_not_gt (n : ℕ) : n ≤ 0 → ¬ n > 0 := by
  exact fun a ↦ (fun {a b} ↦ Nat.not_lt.mpr) a

lemma not_le_imp_gt (n : ℕ) : ¬ n ≤ 0 → n > 0 := by
  exact fun a ↦ (fun {a b} ↦ Nat.not_le.mp) a

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  have ph := even_or_odd n
  obtain ph | ph := ph
  · dsimp [Even] at ph
    obtain ⟨ k, hk ⟩ := ph
    have IH := extract_pow_two k
    have hk2 : ¬ (k ≤ 0) := by
      intro h
      have h :=
        calc
          n = 2 * k := by rw [hk]
          _ ≤ 2 * 0 := by rel [h]
          _ = 0 := by numbers
      have h2 := by exact le_imp_not_gt n h
      contradiction
    have h3 := by exact not_le_imp_gt k hk2
    have h4 := by exact IH h3
    obtain ⟨ a, x, hax ⟩ := h4
    obtain ⟨ hx, ha ⟩ := hax
    use a + 1
    use x
    constructor
    · exact hx
    · rw [hk]
      rw [ha]
      ring
  · use 0, n
    constructor
    · exact ph
    · ring
  
