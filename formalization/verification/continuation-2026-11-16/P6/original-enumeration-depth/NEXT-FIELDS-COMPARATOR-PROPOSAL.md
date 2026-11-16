# Proposed next essential target: original Fields recognizer

Status: design proposal only. No executable AST or Lean comparator is frozen,
no proof authoring is authorized by this note, and no acceptance is claimed.

The ten depth endpoints remove the depth supplier gap. They do not prove the
original `NumberedAuxiliaryEnumeration.Fields` predicate internally. The next
supplier must independently follow that predicate, not define Fields to mean
membership in a chosen enumeration and then claim a characterization by
construction.

## Required independent AST before freezing

Use a fresh boolean structural-recursion layer, with its own answers/cache.
A recursive key must include both the actual raw code and variable bound:
`(raw, variableBound)`. The rank is the raw-code coordinate, not the packed-key
number. Lambda dependencies use `(body, variableBound+1)`; ordinary uses
`(base, variableBound)`; binary and numbered retain the same variable bound
on their ordered children. Original raw-child descent should establish rank
decrease. The four fixed runtime inputs are allowed types, original encoded
heads, labels and tuple bound. The executable graph must not confuse original
encoded-head membership with converted raw-head membership.

This key change is necessary: the already checked depth dependency has a
constant dummy parameter and does not implement the Fields binder-context
update. Reusing its value cache would be unsound.

## Proposed exact native target

For every n, actual source lists S : List Ty and H : List (HeadCode (Fin n)),
labels, tupleBound, variableBound and c : Code (Fin n), the fresh recognizer
on the original numeric encodings returns 1 iff
`NumberedAuxiliaryEnumeration.Fields S H labels tupleBound variableBound c`.
It returns a boolean, and invalid Code decoder outputs return 0. The exact
all-raw extension must be fixed in Definitions before proof development;
malformed list/head encodings must not silently change the typed theorem.

## Proposed internal targets

For each of the eight actual original constructors, acceptance of the fresh
recognizer is equivalent in the original derivation calculus to the literal
Fields branch:

- variable: index < variableBound;
- lambda: actual type membership and child acceptance at variableBound+1;
- application/cons: actual type membership and both child acceptances at the
  same variableBound;
- bottom: actual type membership;
- ordinary: original encoded-head membership and its actual conversion to the
  constructor's raw head, plus base acceptance;
- numbered: label <= labels, original encoded-head membership/conversion,
  result-type membership, base acceptance, actual type-list length <= tuple
  bound, all actual type-list entries in S, and extras acceptance;
- nil: true.

Retain the actual Code-validity premise/split needed by the chosen totalized
recognizer; do not imply malformed constructor inputs are valid typed codes.
All child acceptance witnesses, list observations, type-list membership and
head-conversion witnesses are object-language formulas. No native truth may
be reflected into internal derivations, and no external Fields supplier may
appear as a premise.

## Later integration target, not this first packet

With independently paid Fields and depth, characterize actual original
finite enumeration membership by Fields and depth <= fuel, preserving
variable-bound increment under lambdas. This requires real internal induction
and is not discharged by the native source theorem or the current one-layer
membership characterization.
