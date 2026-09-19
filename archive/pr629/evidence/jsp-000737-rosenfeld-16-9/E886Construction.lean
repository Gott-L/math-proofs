/-
The Erdős–Rosenfeld construction: elementary natural-number identities.

The mathematical construction is due to Paul Erdős and Moshe Rosenfeld
(1997). Definitions and identities are adapted from Jarek Koch's
RosenfeldConstructionV2, at commit
230bf2cd0bc15f971ad9d0e36f36f2056dd9d8b7 of
https://github.com/jarekkoch-hub/erdos887-lean.
This small implementation was prepared with Codex assistance; it makes
no mathematical discovery or first-formalization priority claim.

MIT License

Copyright (c) 2026 Jarek Koch

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import Mathlib.Tactic.Ring

namespace Erdos886

def N (a : ℕ) : ℕ :=
  a * (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) * (a + 6) * (a + 7)

def A0 (a : ℕ) : ℕ := (a + 1) * (a + 2) * (a + 4) * (a + 7)
def B0 (a : ℕ) : ℕ := a * (a + 3) * (a + 5) * (a + 6)
def A1 (a : ℕ) : ℕ := (a + 1) * (a + 2) * (a + 5) * (a + 6)
def B1 (a : ℕ) : ℕ := a * (a + 3) * (a + 4) * (a + 7)
def A2 (a : ℕ) : ℕ := (a + 1) * (a + 3) * (a + 4) * (a + 6)
def B2 (a : ℕ) : ℕ := a * (a + 2) * (a + 5) * (a + 7)
def A3 (a : ℕ) : ℕ := (a + 2) * (a + 3) * (a + 4) * (a + 5)
def B3 (a : ℕ) : ℕ := a * (a + 1) * (a + 6) * (a + 7)

theorem A0_mul_B0 (a : ℕ) : A0 a * B0 a = N a := by
  unfold A0 B0 N
  ring

theorem A1_mul_B1 (a : ℕ) : A1 a * B1 a = N a := by
  unfold A1 B1 N
  ring

theorem A2_mul_B2 (a : ℕ) : A2 a * B2 a = N a := by
  unfold A2 B2 N
  ring

theorem A3_mul_B3 (a : ℕ) : A3 a * B3 a = N a := by
  unfold A3 B3 N
  ring

theorem A0_dvd_N (a : ℕ) : A0 a ∣ N a := ⟨B0 a, (A0_mul_B0 a).symm⟩
theorem A1_dvd_N (a : ℕ) : A1 a ∣ N a := ⟨B1 a, (A1_mul_B1 a).symm⟩
theorem A2_dvd_N (a : ℕ) : A2 a ∣ N a := ⟨B2 a, (A2_mul_B2 a).symm⟩
theorem A3_dvd_N (a : ℕ) : A3 a ∣ N a := ⟨B3 a, (A3_mul_B3 a).symm⟩

theorem B0_lt_A0 (a : ℕ) : B0 a < A0 a := by
  have h : B0 a + (16 * a + 56) = A0 a := by unfold A0 B0; ring
  omega

theorem A0_lt_A1 (a : ℕ) : A0 a < A1 a := by
  have h : A0 a + (2 * a ^ 2 + 6 * a + 4) = A1 a := by unfold A0 A1; ring
  omega

theorem A1_lt_A2 (a : ℕ) : A1 a < A2 a := by
  have h : A1 a + (2 * a ^ 2 + 14 * a + 12) = A2 a := by unfold A1 A2; ring
  omega

theorem A2_lt_A3 (a : ℕ) : A2 a < A3 a := by
  have h : A2 a + (4 * a ^ 2 + 28 * a + 48) = A3 a := by unfold A2 A3; ring
  omega

theorem B0_pos {a : ℕ} (ha : 1 ≤ a) : 0 < B0 a := by
  unfold B0
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos ha (by omega)) (by omega)) (by omega)

theorem self_le_N {a : ℕ} (ha : 1 ≤ a) : a ≤ N a := by
  unfold N
  calc
    a = a * 1 * 1 * 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ a * (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) *
        (a + 6) * (a + 7) := by
      repeat' apply Nat.mul_le_mul
      all_goals omega

theorem N_pos {a : ℕ} (ha : 1 ≤ a) : 0 < N a :=
  lt_of_lt_of_le (by omega) (self_le_N ha)

theorem pow8_le_N (a : ℕ) : a ^ 8 ≤ N a := by
  unfold N
  calc
    a ^ 8 = a * a * a * a * a * a * a * a := by ring
    _ ≤ a * (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) *
        (a + 6) * (a + 7) := by
      repeat' apply Nat.mul_le_mul
      all_goals omega

/-- A cross-pair gap controlling all four divisors above the square root. -/
theorem B0_add_gap_eq_A3 (a : ℕ) : B0 a + 8 * (a + 3) * (a + 5) = A3 a := by
  unfold B0 A3
  ring

end Erdos886
