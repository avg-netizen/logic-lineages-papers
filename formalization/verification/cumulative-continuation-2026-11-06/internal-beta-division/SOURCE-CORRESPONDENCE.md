# Source correspondence

All three targets literally embed OrdinaryArithmetic.betaFormula and
OrdinaryArithmetic.lessFormula. The modulus abbreviation is exactly the
original successor of (successor index) times the second code component.
No changed beta relation, auxiliary order symbol or semantic oracle is used.

Bounded quotient-zero uses the existing original order elimination rule to
obtain the strict-bound witness and introduces the original beta block with
quotient zero. Remainder-bound extraction uses the second equation of that
same original block. The non-wrapping successor step transports the original
quotient equation into fresh-variable contexts and applies the original
addition-successor rule, retaining its quotient and introducing the new bound
witness. Freshness is provided by the previously accepted finite-block/order
elimination rules and checked renaming, not an extra derivation constructor.
