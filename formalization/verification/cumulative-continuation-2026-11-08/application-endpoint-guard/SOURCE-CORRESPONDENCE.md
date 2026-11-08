# Original application endpoint guard: frozen specification

This is a supporting prerequisite for paper06 lem:id1, not promotion of a
numbered source claim. The source is ../06-godel-t-termination-ordering/paper.tex,
lines 537–549 for the function-side application rule and 551–556 for the
least-code quotient/arithmetic edge interpretation. The paper hash is recorded
in FROZEN-SPECIFICATION.json.

## Exact existing endpoint semantics

Both targets refer directly to InternalApplicationStepPeel.endpointValue and
EndpointCalibrated. No alternative predicate, decoder, encoding or calculus is
introduced. The five natural inputs are domain, codomain, function, target and
argument. Domain and codomain are decoded using the original decodeType.
Function and argument use the original decodeUniverse at exactly symbols, S
and Gamma. Target uses ordinary decodePackedNumber at Gamma, with no added
universe filter. Successful outputs must satisfy function type = arrow sigma
tau, target type = arrow sigma tau, argument type = sigma, and tau in S.
Any failed decoder or guard yields zero. All natural input vectors, arbitrary
symbol/window lists and fixed contexts are quantified. No subtype-closure,
valid-window, representative, accepted-certificate or decoding-success premise
is added. Membership tau in S is tested, not inferred from closure.

## Two targets and intended evidence boundary

ActualOriginalEndpointPrimitive proves primitive recursiveness of that exact
old endpointValue. Existing original type, packed and universe decoder
primitive-recursion results may supply its computation. The intended proof
composes the original decoders and finite Boolean equality/membership tests.

ActualOriginalEndpointProgramExists produces one original GorbowPRProgram
Program 5 per fixed n, arity, symbols, S and Gamma, satisfying the existing
EndpointCalibrated on every natural input vector. The intended route applies
the existing allPrimitiveFunctions theorem to the primitive-recursion result.
This is an opaque representability witness with complete external calibration,
not an exposed structurally compositional endpoint decoder AST. No effective
uniform program compiler in the fixed parameters is claimed.

## Explicit exclusions

External calibration is not an internal truth-to-derivability rule. The new
existential does not derive the endpoint leaf graph from typed source formulas,
prove original arithmetic invariant propagation or representative congruence,
assemble joint-context/outer pathValue behavior, establish CertifiedApplicationLift,
or complete paper06 lem:id1. Those obligations remain unpaid. The original
step peel and whole-checker internal equations still retain their explicit
leaf graph premises. No full-root or remote-CI build is claimed.

## Freeze status

Definitions, Targets, Preflight and this correspondence were frozen before
proof authorship and before native preflight. Independent review and successful
native preflight are required before proof authorship. No compiler slot or Git
authority has been granted to this worker.
