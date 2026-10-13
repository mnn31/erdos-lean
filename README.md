# erdos-lean

This repository holds Lean 4 proofs of statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
so that problem files there can point to them with the `formal_proof` attribute. Every file
imports the problem file from formal-conjectures at a pinned commit, except where noted below. Where a proof settles a
statement from that repository, the theorem's type is written as `type_of% <statement>`, its
negation, or the same statement with the `answer(...)` filled in. That way the proved type is
exactly the repository's type, not a restatement of it.

Every module has its own namespace (`ErdosLean.Erdos887`, `ErdosLean.Erdos1180`, ...), so all
of them can be imported together through `ErdosLean.lean`.

## Contents

**`ErdosLean/Erdos887.lean`** is about divisors of `n` in the window `(√n, √n + C n^{1/4})`.
`card_window_le_one` and `card_window_le_four` show that for every `n` the window holds at most
one divisor when `C = 1` and at most four when `C = 2`. `five_divisors_infinite` shows that with
`C = 7/2` infinitely many `n` have at least five divisors in the window, using a Pell family.
These three results are new. `erdos_887_rosenfeld_4_false` refutes
`Erdos887.erdos_887.variants.rosenfeld_4`. That statement lets the constant `C` vary, and with
`C = 40` infinitely many `n` have five divisors in the window, so `4` is not the greatest such
count. This is a refutation of the statement as formalised. The construction was posted on the
erdosproblems.com forum thread for problem 887.

**`ErdosLean/Erdos1180.lean`** refutes `Erdos1180.erdos_1180.variants.optimal`
(`erdos_1180.variants.optimal_refuted`, with the answer-filled form
`erdos_1180.variants.optimal_false`). This is also a refutation of the statement as formalised.
The constant `C ε` there must work for every prime, small ones included. When `p ^ ε < 2` the
only admissible denominator is `1`, so `C ε` grows exponentially in `1 / ε`. The argument needs
the defining set of `C ε` to be nonempty, which is the affirmative answer to the main problem.
For that part the file includes Glibichuk's argument as formalised in
[plby/lean-proofs](https://github.com/plby/lean-proofs) (Apache-2.0), moved to its own namespace.

**`ErdosLean/Erdos269.lean`** answers `Erdos269.erdos_269.variants.rational` in the negative
(`erdos_269.variants.rational_refuted`, `erdos_269.variants.rational_answer`). For `P = {2, 3}`
the series is irrational. This case was proved by Steve Fan on the erdosproblems.com forum in
June 2026, and the factorisation of the series used here is his. This file is an independent
elementary formal proof.

**`ErdosLean/Erdos1054.lean`** answers `Erdos1054.erdos_1054.parts.ii` in the negative
(`erdos_1054_parts_ii_false`, `erdos_1054_parts_ii_solution`). It follows Tao's argument from the
discussion of problem 468 on erdosproblems.com. The Selberg sieve material is vendored, with
only small changes, from Apache-2.0 sources: Arend Mellendijk's Selberg sieve as included in
PrimeNumberTheoremAnd, and the two-dimensional sieve and Brun-Titchmarsh modules of
[antoshashakov/Principia-Math-Solutions](https://github.com/antoshashakov/Principia-Math-Solutions).
Their copyright headers are kept in the file.

**`ErdosLean/Erdos1167.lean`** proves `Erdos1167.erdos_1167.variants.finite_targets`
(`erdos_1167_finite_targets`). The result is due to Erdős, Hajnal, Máté and Rado (1984). The
proof uses the Erdős-Rado tree argument and the stepping-up construction.

**`ErdosLean/Erdos36.lean`** proves `Erdos36.erdos_36.variants.upper` with the answer
`0.380924` filled in (`erdos_36_variants_upper`). It also proves
`Erdos36.minimum_overlap.variants.upper.haugland_2022` (`haugland_2022`). The constant `0.380924`
comes from AlphaEvolve's published 95-step function. The proof turns that function into a
residue-class construction on `{1, ..., 2n}`, and the kernel checks the needed integer
inequalities with `decide +kernel`.

**`ErdosLean/Erdos872.lean`** proves `Erdos872.erdos_872.variants.prime_question`
(`erdos_872_variants_prime_question`): every maximal primitive subset of `{2, ..., n}` has at
least `π(n)` elements. The argument is old-bielefelder's, from post #6532 of the erdosproblems.com
forum thread (May 2026).

**`ErdosLean/Erdos919.lean`** proves the four solved statements of a proposed formal-conjectures
file for Problem 919, which asks for a graph on `ω₂²` with chromatic number `ℵ₂` (or `ℵ₁`) whose
subgraphs on vertex sets of smaller order type are countably chromatic. That file is not in
formal-conjectures at the pinned commit, so the four types are copied from it verbatim.
`erdos_919.variants.iff_erdos_918_i` shows that the `ℵ₂` question is equivalent to
`Erdos918.erdos_918.parts.i`, and an `example` checks by `rfl` that its right-hand side is that
statement. `erdos_919.variants.aleph_1_iff` shows that the `ℵ₁` question is equivalent to the
existence of a graph on `ℵ₂` vertices that is not countably chromatic although all of its
subgraphs on `ℵ₁` vertices are. `erdos_919.variants.aleph_2_imp_aleph_1` and
`erdos_919.variants.aleph_1_of_CH` give a positive answer to the `ℵ₁` question when the `ℵ₂`
question has one, and under CH. The proof blows a graph on `ω₂` up to `ω₂ ×ₗ ω₂`, and the CH case
uses the Erdős-Hajnal shift graph.

## Building

Install [elan](https://github.com/leanprover/elan), then run

```
lake exe cache get
lake build
```

The toolchain in `lean-toolchain` matches formal-conjectures, and `lakefile.toml` pins
formal-conjectures to commit `bdda9748e16d1df263db93d5241011fb399abfae`.

## Axioms

None of the main theorems uses `sorry`, extra axioms, or `native_decide`. `#print axioms` on each
of them reports only `propext`, `Classical.choice` and `Quot.sound`. To check this, run
`lake env lean` on a file such as

```
import ErdosLean

#print axioms ErdosLean.Erdos887.erdos_887_rosenfeld_4_false
#print axioms ErdosLean.Erdos1180.erdos_1180.variants.optimal_refuted
```

## License

Apache-2.0, see `LICENSE`. The vendored sieve code in `Erdos1054.lean` and the Glibichuk
formalisation in `Erdos1180.lean` come from Apache-2.0 projects, as noted above.
