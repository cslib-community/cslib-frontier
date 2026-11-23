/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate


public import CslibFrontier.Computability.Probabilistic.PPT.AuxClock.Basic
public import CslibFrontier.Computability.Probabilistic.Internal.Oracle.AuxClock

/-!
# Probabilistic polynomial-time programs clocked in a designated primary input

In auxiliary-input cryptography (such as Goldreich's definition of auxiliary-input zero knowledge),
a probabilistic machine receives a primary input `a : α` together with an arbitrary, potentially
unbounded auxiliary input word `z : List Bool` on its input tape `encPair input encBits (a, z) =
frame (input a) ++ z`, while its polynomial step bound `c * ((input a).length + 1) ^ d` is a
function of the primary input length `(input a).length` alone.

`IsPPTWithAux` and `IsOraclePPTWithAux` capture this machine contract for closed and oracle
probabilistic programs. Because `frame (input a)` is self-delimiting (`unframe (frame (input a) ++
z) = input a`), a machine can recover the primary input length from the combined input tape without
scanning `z`. Since a machine run under any polynomial-time computable clock is clean
(`Cslib.Probability.IsOraclePPTOn.runOracle_of_clock`), every `IsOraclePPTWithAux`
(resp. `IsPPTWithAux`)
program is automatically a standard `IsOraclePPTOn` (resp. `IsPPTOn`) program on
`encPair input encBits`. Moreover, by the input-tape prefix-locality theorem
(`runOracle_append_take` / `runClosed_append_take`), a run of
`T = c * ((input a).length + 1) ^ d` steps on `frame (input a) ++ z` depends only on `z.take T`.

## Main definitions

* `Cslib.Probability.IsPPTWithAux`: closed uniform strict PPT clocked in the primary input.
* `Cslib.Probability.IsOraclePPTWithAux`: oracle uniform strict PPT clocked in the primary input.

## Main results

* `Cslib.Probability.IsOraclePPTOn.runOracle_of_clock`: any finite-control oracle machine run
  under a polynomial-time computable clock `clock : List Bool → ℕ` is `IsOraclePPTOn`.
* `Cslib.Probability.IsPPTWithAux.of_machine`,
  `Cslib.Probability.IsOraclePPTWithAux.of_machine`: explicit finite-control machine constructors.
* `Cslib.Probability.IsOraclePPTWithAux.isOraclePPTOn`,
  `Cslib.Probability.IsPPTWithAux.isPPTOn`: prefix-clocked programs are standard `IsOraclePPTOn`
  and `IsPPTOn` programs on `encPair input encBits`.
* `Cslib.Probability.computableInPolyTime_take_aux`,
  `Cslib.Probability.IsPPTOn.take_aux`,
  `Cslib.Probability.IsOraclePPTOn.take_aux`: truncating the auxiliary input to length
  `c * ((input a).length + 1) ^ d` preserves `IsPPTOn` and `IsOraclePPTOn`.
* `Cslib.Probability.IsOraclePPTOn.isOraclePPTWithAux_take`,
  `Cslib.Probability.IsPPTOn.isPPTWithAux_take`: truncating the auxiliary input of an
  `IsOraclePPTOn` or `IsPPTOn` program to `c * ((input a).length + 1) ^ d` upgrades it to
  `IsOraclePPTWithAux` or `IsPPTWithAux` clocked in `a` alone.
* `Cslib.Probability.IsPPTWithAux.length_le`,
  `Cslib.Probability.IsOraclePPTWithAux.length_le`: supported encoded outputs are bounded by a
  polynomial in the primary input length `(input a).length`, uniformly over all `z`.
* `Cslib.Probability.IsOraclePPTWithAux.exists_run_interpret_take`,
  `Cslib.Probability.IsPPTWithAux.exists_eval_take`: a prefix-clocked program on `(a, z)` has the
  exact same semantics as on `(a, z.take m)` for every `m ≥ c * ((input a).length + 1) ^ d`.
* `Cslib.Probability.IsPPTWithAux.preprocess`,
  `Cslib.Probability.IsOraclePPTWithAux.preprocess`: polynomial-time primary-input preprocessing
  for `IsPPTWithAux` and `IsOraclePPTWithAux`.
-/
