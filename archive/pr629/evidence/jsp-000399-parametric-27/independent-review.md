# Internal independent review: a 27-element triple-sum collision

Review date: 2026-09-17. This sibling agent independently evaluated the proposed numerical witnesses. This is an internal check in the same assistant/tool environment, not independent human peer review or official prize approval. No claim of novelty or first formalization is made.

## Exact positive witnesses

```text
A = [1, 44, 48, 60, 68, 96, 104, 109, 116, 120, 145, 157, 161, 163, 165, 169, 181, 204, 212, 217, 224, 228, 260, 264, 276, 284, 325]
B = [1, 42, 50, 62, 66, 98, 102, 109, 114, 122, 145, 157, 161, 163, 165, 169, 181, 206, 210, 217, 222, 230, 258, 266, 278, 282, 325]
```

Each list contains 27 distinct positive integers, all in [1,325]. Both sums are 4401. The underlying sets differ: 44 belongs to A but not B, while 42 belongs to B but not A. B is the increasing rearrangement of {326-a : a in A}.

Independent integer enumeration with `itertools.combinations(values, 3)` examines unordered triples of distinct entries, once each. Each side has C(27,3) = 2925 entries in its sum multiset. Exact `Counter` comparison returned no mismatched coefficients. The common spectrum has 563 different values, minimum 93, maximum 885, and maximum multiplicity 45, attained at 489.

The common multiplicity histogram is:

```text
multiplicity: number of different sums with that multiplicity
1:108, 2:146, 3:10, 4:56, 5:60, 6:52, 7:16,
8:42, 15:34, 16:12, 17:18, 19:2, 20:6, 45:1
```

SHA-256 of the sorted 2925-entry spectrum, encoded as decimal integers separated by commas and followed by one LF newline:

```text
6278afbc6f85389a7d2abad5fb0cbe82be59054caddc94438a6455550af9206c
```

SHA-256 of the nonzero frequency list, encoded as ascending `sum:count` lines followed by one final LF newline:

```text
0dd7c00af1ae5f25c8b386844a6806118f03bc11e2f131b248b0fc5d3f123174
```

These digests identify the computed data; the exact arithmetic checks and algebra below establish the identity.

## An elementary algebraic verification

This proof verifies the same concrete example without enumerating all 2925 triples. It is a verification of a supplied construction, with no priority claim.

Set r = (1,3,9,27,81). Before the translation by 163, the 27 entries in A are the eleven entries 0 and +/-2r_i, together with the sixteen signed sums sum(epsilon_i r_i) whose five signs have product +1. B before translation uses product -1 instead. Direct integer comparison confirmed both descriptions against the supplied lists. Negating all five signs interchanges their products, and the eleven common entries are invariant under negation.

Work in the Laurent polynomial ring Q[z,z^(-1)]. Define

```text
u_i = z^(r_i) + z^(-r_i),        v_i = u_i^2,
T = product u_i,                D = product (z^(r_i)-z^(-r_i)),
C = sum v_i - 9,
P_+ = C + (T+D)/2,              P_- = C + (T-D)/2.
```

Here C is precisely the generating polynomial of the eleven common entries, because v_i = z^(2r_i)+2+z^(-2r_i). The half-products select the desired sign parities, so P_+ and P_- generate the two 27-entry lists.

For any list with generating polynomial P, write E_3(P) for the generating polynomial of its three-element index-subset sums. Expanding P^3 and separating the terms with repeated indices gives Newton's identity

```text
6 E_3(P)(z) = P(z)^3 - 3 P(z)P(z^2) + 2 P(z^3).
```

Let e_1 = sum v_i and e_2 = sum_{i<j} v_i v_j. The elementary identities needed for substitution are

```text
D(z^2) = D T,
T(z^2) = product (v_i-2),
D(z^3) = D product (v_i-1),
D^2 = product (v_i-4),          T^2 = product v_i,
C(z^2) = sum v_i^2 - 4e_1 + 11.
```

Subtracting Newton's identity for P_- from that for P_+ and collecting terms yields

```text
6(E_3(P_+) - E_3(P_-)) = D [6e_2 - 42e_1 + 210 + L/4],
L = -3 product v_i + product (v_i-4)
    -6 product (v_i-2) + 8 product (v_i-1).
```

Expanding each five-factor product shows exactly

```text
L = -24e_2 + 168e_1 - 840.
```

For completeness, the coefficients on elementary symmetric terms of degrees 5,4,3,2,1,0 are respectively (0,0,0,-24,168,-840). Thus the bracket vanishes identically and E_3(P_+) = E_3(P_-). Translating every entry by 163 multiplies both triple-sum polynomials by z^489, preserving their equality. The numerical distinctness checks ensure that index-subsets here are subsets of 27 different integers. This proves equality including every multiplicity.

## Complete coefficient certificate

Let c_s be the common number of triples with sum s. Coefficients outside [93,885] are zero. The center coefficient is c_489 = 45. For 93 <= s <= 488, the following rows give every coefficient consecutively, including zeros. The remaining coefficients are c_(978-s) = c_s. Consequently this table specifies the entire 2925-term multiset exactly.

```text
93..116: 1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0
117..140: 1,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0
141..164: 1,0,0,0,1,0,0,0,1,0,0,1,1,1,0,0,1,1,0,1,1,0,0,0
165..188: 4,0,0,0,1,1,0,1,1,0,0,1,1,1,0,0,1,0,0,0,1,0,0,1
189..212: 1,1,0,0,0,1,0,1,0,0,0,1,2,1,0,1,0,4,0,4,0,2,0,4
213..236: 2,4,0,1,2,2,0,2,2,1,0,4,2,4,0,2,0,4,0,4,0,1,0,1
237..260: 3,1,0,0,0,2,0,2,0,0,0,2,4,2,0,0,4,1,2,1,4,1,0,4
261..284: 5,4,0,2,4,4,2,4,5,1,2,2,15,2,2,1,5,4,2,4,4,2,0,4
285..308: 6,4,0,1,5,1,2,1,5,0,0,2,6,2,0,0,4,2,2,2,5,0,2,1
309..332: 16,1,2,1,6,5,2,5,6,2,2,5,16,5,2,1,16,2,8,2,16,1,2,5
333..356: 16,5,2,2,6,5,2,5,6,1,2,2,16,2,2,1,5,5,2,5,4,2,0,5
357..380: 7,5,0,2,6,5,2,5,6,5,0,15,7,15,0,8,5,15,2,15,6,6,2,8
381..404: 19,8,2,6,6,15,2,15,5,8,0,15,7,15,0,5,6,6,2,6,6,3,0,8
405..428: 7,8,0,4,4,8,2,8,5,3,2,6,17,6,2,5,6,15,2,15,6,8,2,15
429..452: 17,15,2,6,17,8,8,8,17,6,2,15,17,15,2,8,7,15,2,15,7,5,2,5
453..476: 20,5,2,2,7,6,2,6,7,2,2,6,17,6,2,1,17,3,8,3,17,2,2,8
477..488: 20,8,2,4,17,8,8,8,20,2,8,4
```

## Lean implementation status and authorship

The independent arithmetic and algebraic reviews above are complete. Subsequently, the author of this note implemented `Jsp399Parametric.lean`; therefore the discussion of that module below is an author verification, not an independent review of its own code. Other agents supplied `Jsp399TripleCore.lean`, `Jsp399Witness.lean`, `EncodedCoeffCertificate.lean`, and the initial versions of the bounded encoding injectivity and permutation-reflection lemmas. All agents used the same assistant/tool environment. Their checks are not official prize adjudication or independent human peer review.

The final `Jsp399Parametric.lean` source was actually compiled with Lean 4.19.0, warnings treated as errors, after its three imported modules had been compiled. The command, run in this directory with the Lean executable on PATH, is:

```powershell
$env:LEAN_PATH='.'
lean -s 65536 -DwarningAsError=true -o Jsp399Parametric.olean Jsp399Parametric.lean
```

The run exited successfully. Source SHA-256:

```text
fd486be111060dafac013d577fc75152b4ff1139187f5def7332efd15d832e77
```

The exact bridge and endpoints are:

- `JSP399TwentySeven.triples_complete`, `triples_nodup`, and `triples_length` state that the list enumerates each increasing triple of distinct indices exactly once, with length 2925. Mapping the sum retains repeated numerical sums.
- `JSP399CoeffCertificate.encoded_triple_sums_perm` certifies equality up to permutation of the two complete spectra of base-13 integer codes. Its generated numeric equalities are checked by Lean's kernel. The generic merge proofs preserve every list entry even when fuel is exhausted, so the proof does not depend on an unproved sorting property.
- `JSP399Parametric.codeA_matches` and `codeB_matches` correlate every one of the 27 literal codes with the corresponding five-dimensional coefficient vector. `encode_triple` and `encoded_sums` identify the code of each vector sum with its scalar triple sum, including the offsets.
- `vectorA_bounds`, `vectorB_bounds`, and `triple_bounds` prove that all source coordinates lie in [-2,2] and all triple coordinates lie in [-6,6]. `encodeCoeff_inj` proves base-13 injectivity on these bounds. `perm_of_map_injOn` lifts a permutation of encoded lists back to a permutation of the bounded vector lists. Thus `vector_triple_sums_perm` proves the full coefficient-vector identity, not only one numerical evaluation.
- `every_additive_image_collision` transports this vector identity through any map to a type with addition satisfying the displayed additivity hypothesis. `every_parameter_collision` specializes it to every tuple of five integer parameters. `every_translated_parameter_collision` additionally permits an arbitrary common integer translation. These identities allow repeated evaluated entries; `collision_with_distinct_entries` explicitly includes the conditions needed when the entries are interpreted as ordinary sets.
- `example_is_nontrivial_collision` verifies the particular 27-entry positive integer collision displayed above, including both lengths, both no-duplicates properties, positivity, full triple-spectrum permutation, and inequality of the underlying sets. `exampleA_matches` ties its first list to the displayed witness; `exampleB_matches_reverse` ties its second list to the reverse of the displayed increasing witness B.

The five audited endpoints `vector_triple_sums_perm`, `every_additive_image_collision`, `every_parameter_collision`, `every_translated_parameter_collision`, and `example_is_nontrivial_collision` each reported exactly the standard logical axioms `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom axiom, or native-evaluation axiom was reported. The source contains no `sorry`, `native_decide`, or custom `axiom` declaration. This is not a claim of an axiom-free proof.

The parameter-family scope is stronger than checking this one witness, but no mathematical novelty, prize eligibility, or first-formalization conclusion follows from that observation. A prior public Lean proof of a 27-element collision is identified in the accompanying README and must be considered in any submission assessment.
