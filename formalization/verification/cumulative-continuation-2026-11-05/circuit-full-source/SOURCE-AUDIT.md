# Literal circuit encoding: allocation and run semantics

Status: exact native gate and standard-axiom audit passed. Parent adoption and independent review remain separate. The final gate is `circuit-full-gates/RECEIPT.json` (source receipt 1793883081665591089-2). All eight owned Lean files and the 404-module local source closure match successful native receipt rows; see `CIRCUIT-FULL-ACCEPTANCE.json`.

## Frozen semantic endpoint

The existing `CircuitLinear.Targets.FullCircuitEncoding` is unchanged. It requires the actual `encodeCircuitSystem c` to be well formed and its actual shared `N[X]` polynomial satisfiability to be equivalent to output equality of the existing positive straight-line circuit run. The source predicate, source theorem, or final target is never added as an assumption.

The four fresh supporting contracts were hashed before proof authoring in `CIRCUIT-FULL-TARGET-FREEZE.json`. Target-only preflight passed in `circuit-full-preflight/RECEIPT.json`.

## Literal allocation

- Original wires occupy `[0,n+g)` once, with input slack wires in `[n+g,n+g+n)`.
- Each of the g gate positions reserves four scalar wires and three four-polynomial square witness blocks, independently of its tag.
- The final nine wires contain V, extra, and seven geometric-polynomial witnesses.
- `Slot` records these exact address ranges. `slot_index_injective` proves every distinct slot has a distinct natural address; `slot_index_bound` proves the declared dimension bounds all of them.
- `allocate` extends these tagged values into one global `Nat → NPolynomial` function. Every row occurrence at a given natural address therefore reads the same value. Repeated x/y inputs are not copied or existentially chosen again.
- `scalar_slots_cover` identifies exactly the original, slack, and reserved scalar slots in the constant-forced prefix. The twelve-per-gate geometric witness block and final seven geometric witnesses are outside that prefix.

## Forward direction

The ordinary gate equations use the original constant convention k↦k+1. The three multiplication square witnesses use triangular values for x, y, and x+y. The literal linear relation between those three triangular values supplies x*y. The existing exact square theorem supplies the actual unrestricted N[X] witnesses.

After the entire scalar prefix has been fixed, the existing simultaneous-constant theorem supplies one V, extra, and seven polynomial witnesses for the final six constant rows. Disjoint allocation leaves all original and previously fixed square values unchanged. Positive input i supplies slack v(i)-1, including slack zero when input i equals one. Unused scalar reserves are zero and unused polynomial reserves may be arbitrary supplied witnesses.

## Backward direction

The last six rows force every value in the scalar prefix to be a natural constant. The one shared extracted assignment is v(i)=coefficient_0(p(i)). Input rows force v(i)=v(slack(i))+1, hence positivity without deleting zero-slack cases. Constant and addition gate rows decode directly; three exact square instances and the two linear multiplication rows force the original product. The same output references force the original output equality.

## Existing run and guard boundary

`ScalarRunSemantics` compares the intermediate natural equations with the existing `CircuitReduction.run`, not a replacement evaluator. Well-formed earlier-wire references guarantee positivity propagates and the extracted positive assignment is a fixed point of that run. Forward run correctness preserves the finite original wire block.

The accepted `circuit_system_wellFormed` is used before the accepted `raw_system_faithful` codec equivalence. Thus filtering malformed references is never used semantically. `encodedPolynomialSolvable` retains its separate original well-formedness guard. This package does not claim the separate numeric circuit codec or Nat-root-to-positive input transport; those remain separately gated dependencies.

## Ownership and checking

Only fresh `CircuitFull*.lean` sources and this verification directory are owned by this package. The frozen CircuitLinear, CircuitBridge, CircuitGadget, and numeric sources are not edited here. All Lean executions use the shared bounded checker and a fresh coordinator grant. No publication is performed.
