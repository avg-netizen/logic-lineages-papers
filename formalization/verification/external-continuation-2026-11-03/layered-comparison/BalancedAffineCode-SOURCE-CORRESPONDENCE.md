# Balanced affine numeric constructors

Draft specification for root review. No candidate proof, comparator receipt,
freeze, or acceptance is asserted by this document.

## Source and exact scope

Source: `08-multivariate-collapse-comparison/paper.tex`, `eq:balanced-atoms`,
`thm:balanced`, and `eq:balanced-row` (lines 950–1026 in the reviewed source).
The source's complete norm input is
`N(lambda) + offset + sum_j (storedFactor_j + 1) * B_j`.
The head-free and all-cancelled remainder, and all large-branch affine guards,
use the actual ordered common basis at the preceding level. Repeated basis
entries and shared raw variables are not independent parameters.

The already accepted `BalancedAffineSyntaxDefinitions` supplies the literal
same-certificate numeral, addition, finite repeated addition, combination,
`lowerPart`, and `completeInput` source expressions. This component specifies
numeric constructors with exact equality to their existing
`BalancedEvaluation.encodeSyntax` codes. It does not redefine that syntax,
the certificate, its semantics, its support, or its atom codec.

## Literal numeric equations

Write `U(E) = BalancedEvaluation.upperData E`,
`Cdata(C) = BalancedEvaluation.certificateData C`, and
`A(a) = (Encodable.decode a : Option BalancedEvaluation.AtomData).getD (0,0,0,[])`.
Every tuple below uses the existing `UpperData` or `AtomData` Encodable instance.

- At shape `[]`, `numeral [] n = 4*n` and
  `add [] E F = 4*Nat.pair E F+2`, exactly `BaseTerm.encode`.
- At shape `k::Gamma`, `numeral (k::Gamma) n` encodes
  `(n, List.replicate k 0, [])`.
- At shape `k::Gamma`, `add (k::Gamma) E F` encodes
  `(U(E).constant + U(F).constant,
  range(k).map (fun j => U(E).outside.getD j 0 + U(F).outside.getD j 0),
  U(E).atoms ++ U(F).atoms)`.
- `scale Gamma n E = (List.replicate n E).foldr (add Gamma) (numeral Gamma 0)`.
  This is the exact literal source tree, including the final zero numeral.
  Scale zero has no atom payloads. Positive scale repeats the ordered original
  payloads rather than collecting, sorting, or changing stored coefficients.
- `combination Gamma k c coefficients basis` is
  `add Gamma (numeral Gamma c)` applied to the right fold, from zero, of
  `range(k).map (fun j => scale Gamma (coefficients.getD j 0) (basis.getD j 0))`.
- `lowerPart k Gamma C E` is that combination with constant and outside vector
  from `U(E)` and basis list `Cdata(C).2`.
- `completeInput k Gamma C a` is that combination with constant
  `rawNormCode A(a).head + A(a).offset`, coefficient list
  `range(k).map (fun j => A(a).factors.getD j 0+1)`, and the SAME basis list
  `Cdata(C).2`. The stored outer coefficient `A(a).1` is ignored, as required
  for an atom's input. Calibration quantifies arbitrary `q` and uses exactly
  `Encodable.encode (BalancedEvaluation.encodeAtom (q,a))`.

At positive shapes, addition constructs exactly `k` outside entries and
preserves every stored atom payload, its original outer coefficient `q`
(representing `q+1`), order, and duplicate. Each factor remains stored as before;
only the complete-input coefficient reads it as factor plus one. Empty bases
and the BASE target shape are included in every applicable target.

## Totalization and primitive recursion

The functions are total on raw naturals and finite lists. The existing upper
and certificate decoders retain their defaults. Failed atom decode uses
`(0,0,0,[])`. Short outside/coefficient lists use zero, short factor lists
use stored zero and hence positive coefficient one, and short basis lists
use raw code zero. Extra vector entries are ignored beyond the declared size.
These are numeric totalization choices, not a validity assertion about any
malformed input or a promise that raw code zero is a numeral at every shape.

`UniformPrimitiveRecursive` quantifies over shape, size, numeric codes, and
finite lists together. The intended proof uses the existing primitive
recursive encode/decode, arithmetic, range/map/fold and list operations, plus
the already established `rawNormCodePrimitiveRecursive`. It must not assume
an evaluator, supply a new norm oracle, or prove only separate fixed-parameter
instances. `noncomputable` on `completeInput` reflects the existing norm
definition; the stated primitive-recursion theorem is an independent obligation.

## Four frozen-target proposals

1. `ExactLiteralOperations`: exact code equality for numeral, add, and scale
   with the existing `BalancedSyntax.Affine` operations at every shape.
2. `ExactFiniteCombination`: exact code equality for a finite ordered basis,
   arbitrary coefficients, and arbitrary source terms.
3. `ExactActualLowerAndInputs`: exact codes of the existing actual `lowerPart`
   and `completeInput`, using one original encoded certificate and its basis.
4. `UniformPrimitiveRecursive`: all six constructors are uniformly primitive
   recursive on all inputs, including malformed numeric codes.

No proof candidate exists at this draft stage. Full balanced formula
construction, finite-exception enumeration, head comparison/collection
programs, the recursive translation, and Snyatkov decidability remain separate.
This component adds no evaluator and makes no whole-compiler claim.
