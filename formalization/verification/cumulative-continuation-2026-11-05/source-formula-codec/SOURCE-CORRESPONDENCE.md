# Total literal source codec and raw-code decisions

SourceFormula uses its original radix-five encoding, with the already established
radix-four BaseTerm decoder. Both source roundtrips are required. Consequently
every natural code is canonical for exactly one literal source formula; this is
not a new fallback interpretation of malformed data.

The six targets extend the existing payload and parameterized source block
decisions to every raw natural input. The exact rejection test remains literal
quantifier-free source-body membership. This does not assert that every raw row
code or every unrelated arithmetic/system encoding is canonical. It also does
not add QE, alternating quantifiers, hyperPhi support or the full BASE result.
