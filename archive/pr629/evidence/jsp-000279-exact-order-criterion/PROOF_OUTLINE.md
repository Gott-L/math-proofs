# Proof outline for the exact-order criterion

All lists below are finite lists of natural numbers from `A`, with repetitions
allowed. Their lengths count summands, including summands equal to zero.

1. **Balanced differences.** An integer `z` is a balanced difference if it is
   `sum(xs)-sum(ys)` for two such lists of equal length. Empty lists give zero;
   concatenation gives addition; swapping lists gives negation. Induction gives
   multiplication by a natural number. Every unsigned difference between two
   elements of `A` is balanced by orienting the two singleton lists.

2. **Extract one from the actual gcd condition.** If the all-divisors condition
   holds, there is a positive natural balanced difference: otherwise every
   pairwise distance is zero and even zero is a common divisor, a contradiction.
   Choose the least positive balanced difference `d`. For any nonnegative
   balanced difference `v`, its remainder `v % d` is balanced, since it is
   `v - (v/d)*d`. A positive remainder would be smaller than `d`. Thus `d`
   divides every pairwise distance, so the given gcd condition forces `d=1`.
   The witnesses for this balanced difference are actual finite lists.

3. **Adjacent lengths.** The gcd condition also gives an element `a ∈ A`.
   Multiply the balanced difference one by `a`. This produces equal-length
   lists `xs,ys` with `sum(xs)-sum(ys)=a`. Append the single element `a` to
   `ys`. The resulting two lists have the same sum `M` and lengths `L,L+1`.
   The argument includes `a=0` and permits the short list to be empty.

4. **Uniform padding.** Suppose the original basis bound is `r`, beyond a
   threshold `N`. For a sufficiently large `n`, represent `n-r*M` with `j≤r`
   summands. Take `j` short copies and `r-j` long copies of the equal-sum
   certificate. These add `r*M` to the sum and `r*(L+1)-j` to the length.
   The combined representation has exactly `r*(L+1)` terms. The threshold
   `N+r*M` suffices. The least working exact count then exists by well-ordering;
   the displayed count is a valid count, not a claim about the minimum.

5. **Necessity and the sequence statement.** If `d` divides every pairwise
   distance, equal-length lists have congruent sums modulo `d`. Exact
   representations of `N` and `N+1` imply `d | 1`. For a strictly increasing
   sequence, consecutive divisibility gives congruence of every term with the
   first by induction; this is equivalent to divisibility of every pairwise
   distance in its range. Finally, an empty list sums to zero, so exact count
   zero cannot work eventually.

This implements the known Erdős–Graham characterization. The least-positive
balanced-difference argument replaces an explicit finite Bézout coefficient
vector; no arithmetic extraction or finite-certificate premise is left in the
final theorem. It establishes neither an optimal order bound nor the separate
extremal-limit statement in the catalogue.
