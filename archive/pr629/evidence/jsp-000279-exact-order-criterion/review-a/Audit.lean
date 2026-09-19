/- Internal AI-team review. The reviewer authored Defs, Padding and Necessity,
but did not author Differences or Criterion. These independently transcribed
statements check the semantic interfaces; they are not an external human review. -/
import E336Criterion

namespace E336InternalReview

theorem raw_set_least_order_iff (A : Set ℕ) (r : ℕ)
    (hb : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, k ≤ r ∧
      ∃ xs : List ℕ, xs.length = k ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) :
    (∃ h : ℕ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
        xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) ∧
      ∀ j : ℕ, j < h → ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ xs : List ℕ, xs.length = j ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n)) ↔
    ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1 :=
  E336.erdos_graham_set_criterion hb

theorem raw_sequence_least_order_iff (a : ℕ → ℕ) (r : ℕ) (ha : StrictMono a)
    (hb : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, k ≤ r ∧
      ∃ xs : List ℕ, xs.length = k ∧
        (∀ x ∈ xs, x ∈ Set.range a) ∧ xs.sum = n) :
    (∃ h : ℕ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
        xs.length = h ∧ (∀ x ∈ xs, x ∈ Set.range a) ∧ xs.sum = n) ∧
      ∀ j : ℕ, j < h → ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ xs : List ℕ, xs.length = j ∧
          (∀ x ∈ xs, x ∈ Set.range a) ∧ xs.sum = n)) ↔
    ∀ d : ℕ, (∀ i : ℕ, d ∣ a (i + 1) - a i) → d = 1 :=
  E336.erdos_graham_sequence_criterion ha hb

theorem raw_set_sufficiency (A : Set ℕ) (r : ℕ)
    (hb : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, k ≤ r ∧
      ∃ xs : List ℕ, xs.length = k ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n)
    (hg : ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1) :
    ∃ h N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
      xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n :=
  (E336.exists_eventuallyExactly_iff hb).mpr hg

theorem raw_set_necessity (A : Set ℕ) (h : ℕ)
    (he : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
      xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) :
    ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1 :=
  E336.differenceGcdOne_of_eventuallyExactly he

theorem raw_gcd_constructs_finite_certificate (A : Set ℕ)
    (hg : ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1) :
    ∃ L M : ℕ,
      (∃ xs : List ℕ, xs.length = L ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = M) ∧
      (∃ ys : List ℕ, ys.length = L + 1 ∧ (∀ y ∈ ys, y ∈ A) ∧ ys.sum = M) :=
  E336.adjacentLengths_of_differenceGcdOne hg

theorem raw_balanced_difference_one (A : Set ℕ)
    (hg : ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1) :
    ∃ xs ys : List ℕ, (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ A) ∧
      xs.length = ys.length ∧ (xs.sum : ℤ) - (ys.sum : ℤ) = 1 :=
  E336.balancedDifference_one hg

theorem raw_padding (A : Set ℕ) (r L M : ℕ)
    (hb : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, k ≤ r ∧
      ∃ xs : List ℕ, xs.length = k ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n)
    (hs : ∃ xs : List ℕ, xs.length = L ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = M)
    (hl : ∃ xs : List ℕ, xs.length = L + 1 ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = M) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
      xs.length = r * (L + 1) ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n :=
  E336.eventuallyExactly_of_adjacent_representations hb hs hl

theorem raw_same_common_divisors (a : ℕ → ℕ) (ha : StrictMono a) (d : ℕ) :
    (∀ x ∈ Set.range a, ∀ y ∈ Set.range a, d ∣ Nat.dist x y) ↔
      ∀ i : ℕ, d ∣ a (i + 1) - a i :=
  E336.pairwise_dvd_iff_consecutive_dvd ha d

theorem raw_positive_exact_count (A : Set ℕ) (h : ℕ)
    (he : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
      xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) : 0 < h :=
  E336.eventuallyExactly_pos he

theorem repetitions_are_permitted : E336.RepresentsExactly ({2} : Set ℕ) 2 4 := by
  refine ⟨[2, 2], rfl, ?_, rfl⟩
  intro x hx
  have hx2 : x = 2 := by simpa using hx
  subst x
  rfl

theorem zero_terms_are_permitted : E336.RepresentsExactly ({0} : Set ℕ) 3 0 := by
  refine ⟨[0, 0, 0], rfl, ?_, rfl⟩
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  rfl

theorem zero_count_is_not_an_eventual_basis (A : Set ℕ) :
    ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ xs : List ℕ,
      xs.length = 0 ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n) := by
  intro h
  exact Nat.lt_irrefl 0 (E336.eventuallyExactly_pos h)

end E336InternalReview
