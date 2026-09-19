import E336Criterion

-- Literal set formulation: bounded list length is the entire basis hypothesis.
example (A : Set ℕ) (r : ℕ)
    (hA : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ h : ℕ, h ≤ r ∧
      ∃ xs : List ℕ, xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) :
    (∃ h N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ xs : List ℕ, xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) ↔
      (∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1) := by
  exact E336.exists_eventuallyExactly_iff hA

-- The least order is obtained, rather than an assumed choice of an exact order.
example (A : Set ℕ) (r : ℕ) (hA : E336.EventuallyAtMost A r) :
    (∃ h : ℕ, (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ xs : List ℕ, xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) ∧
      ∀ j : ℕ, j < h → ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ xs : List ℕ, xs.length = j ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n)) ↔
      (∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1) := by
  exact E336.erdos_graham_set_criterion hA

-- Consecutive differences of the actual sequence range, not a larger set.
example (a : ℕ → ℕ) (r : ℕ) (ha : StrictMono a)
    (hA : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ h : ℕ, h ≤ r ∧
      ∃ xs : List ℕ, xs.length = h ∧ (∀ x ∈ xs, ∃ i : ℕ, a i = x) ∧ xs.sum = n) :
    (∃ h : ℕ, E336.HasExactOrder (Set.range a) h) ↔
      (∀ d : ℕ, (∀ i : ℕ, d ∣ a (i + 1) - a i) → d = 1) := by
  exact E336.erdos_graham_sequence_criterion ha hA

-- The finite adjacent-length certificate follows from the full divisibility condition.
example (A : Set ℕ)
    (hg : ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1) :
    ∃ L M : ℕ,
      (∃ xs : List ℕ, xs.length = L ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = M) ∧
      (∃ ys : List ℕ, ys.length = L + 1 ∧ (∀ y ∈ ys, y ∈ A) ∧ ys.sum = M) := by
  exact E336.adjacentLengths_of_differenceGcdOne hg

-- Explicit padding bound; the same number M is represented by both lengths.
example (A : Set ℕ) (r L M : ℕ) (hA : E336.EventuallyAtMost A r)
    (hs : E336.RepresentsExactly A L M) (hl : E336.RepresentsExactly A (L + 1) M) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
      xs.length = r * (L + 1) ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n := by
  exact E336.eventuallyExactly_of_adjacent_representations hA hs hl

-- The definitions permit repeated summands.
example (A : Set ℕ) (a : ℕ) (ha : a ∈ A) : E336.RepresentsExactly A 2 (a + a) := by
  exact ⟨[a, a], rfl, by simpa using ha, by simp⟩

-- Empty lists are allowed; they cannot be an eventual exact order.
example (A : Set ℕ) : E336.RepresentsExactly A 0 0 := E336.representsExactly_zero A
example (A : Set ℕ) : ¬ E336.EventuallyExactly A 0 := by
  intro h
  have := E336.eventuallyExactly_pos h
  omega
