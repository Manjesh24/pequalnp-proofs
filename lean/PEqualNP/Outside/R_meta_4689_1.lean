import Mathlib
import PEqualNP.Defs

open Nat

theorem PEqualNP.Outside.R_meta_4689_1
    (hcubic : ∀ (a b : ℕ), a ≤ b → a + b - 1 ≤ 4512 →
        (24 * (a + b - 1) + 1) * (24 * a + 23 * b - 23) > b * (a * (a - 1)))
    (hcubic' : ∀ (a b : ℕ), b ≤ a → a + b - 1 ≤ 4512 →
        (24 * (a + b - 1) + 1) * (23 * a + 24 * b - 23) > a * (b * (b - 1))) :
    ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) → x4 ≤ x2 * x3 →
      x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) → x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) →
      x4 ≤ (24 : ℕ) * x1 := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 h5
  have hbound : x2 + x3 - 1 ≤ 4512 := by omega
  by_cases hx2 : x2 = 0
  · have hz : x4 = 0 := by nlinarith [h3]
    omega
  by_cases hx3 : x3 = 0
  · have hz : x4 = 0 := by nlinarith [h3]
    omega
  by_cases hle : x4 ≤ x3
  · -- the small case: x4 ≤ x3 ≤ x2 + x3 - 1 ≤ x1 ≤ 24 * x1
    omega
  have hgt : x3 < x4 := by omega
  by_cases hab : x2 ≤ x3
  · -- x2 ≤ x3: the first counting inequality is the tight one
    have h4' : x4 * x4 ≤ x3 * (x2 * (x2 - 1)) + x3 * x4 := by
      have hdist : x3 * (x2 * (x2 - 1) + x4) = x3 * (x2 * (x2 - 1)) + x3 * x4 :=
        Nat.mul_add _ _ _
      rw [hdist] at h4
      exact h4
    have hkey : x4 * (x4 - x3) ≤ x3 * (x2 * (x2 - 1)) := by
      rw [Nat.mul_sub]
      exact (Nat.sub_le_iff_le_add).2 (by simpa only [Nat.add_comm, Nat.mul_comm] using h4')
    by_contra hcon
    push_neg at hcon
    have h24 : (24 : ℕ) * (x2 + x3 - 1) + 1 ≤ x4 := by omega
    have hq : (24 : ℕ) * x2 + 23 * x3 - 23 ≤ x4 - x3 := by omega
    have hmul : (24 * (x2 + x3 - 1) + 1) * (24 * x2 + 23 * x3 - 23) ≤ x4 * (x4 - x3) := by
      exact Nat.mul_le_mul h24 hq
    have hc := hcubic x2 x3 hab hbound
    have hBC : x3 * (x2 * (x2 - 1)) < x4 * (x4 - x3) := lt_of_lt_of_le hc hmul
    have hBB : x3 * (x2 * (x2 - 1)) < x3 * (x2 * (x2 - 1)) := lt_of_lt_of_le hBC hkey
    exact Nat.lt_irrefl _ hBB
  · -- x3 < x2: the second counting inequality is the tight one
    have h5' : x4 * x4 ≤ x2 * (x3 * (x3 - 1)) + x2 * x4 := by
      have hdist : x2 * (x3 * (x3 - 1) + x4) = x2 * (x3 * (x3 - 1)) + x2 * x4 :=
        Nat.mul_add _ _ _
      rw [hdist] at h5
      exact h5
    have hkey : x4 * (x4 - x2) ≤ x2 * (x3 * (x3 - 1)) := by
      by_cases hx : x2 ≤ x4
      · rw [Nat.mul_sub]
        exact (Nat.sub_le_iff_le_add).2 (by simpa only [Nat.add_comm, Nat.mul_comm] using h5')
      · have hz : x4 * (x4 - x2) = 0 := by
          have hz' : x4 - x2 = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hx)
          simp [hz']
        omega
    by_contra hcon
    push_neg at hcon
    have h24 : (24 : ℕ) * (x2 + x3 - 1) + 1 ≤ x4 := by omega
    have hq : (23 : ℕ) * x2 + 24 * x3 - 23 ≤ x4 - x2 := by omega
    have hmul : (24 * (x2 + x3 - 1) + 1) * (23 * x2 + 24 * x3 - 23) ≤ x4 * (x4 - x2) := by
      exact Nat.mul_le_mul h24 hq
    have hc := hcubic' x2 x3 (by omega) hbound
    have hBC : x2 * (x3 * (x3 - 1)) < x4 * (x4 - x2) := lt_of_lt_of_le hc hmul
    have hBB : x2 * (x3 * (x3 - 1)) < x2 * (x3 * (x3 - 1)) := lt_of_lt_of_le hBC hkey
    exact Nat.lt_irrefl _ hBB
