# Narendran bridge source and scope audit

The two input languages are different. DiophantineCompletion uses an explicit
integer polynomial with natural roots. FunctionalHardnessCompletion uses a
finite fixed-integer-coefficient linear system over shared unknowns in N[X].
The checked H10 theorem cannot be substituted directly for the latter supplier.

Primary references:
- Narendran, LICS 1996, pp.466–472, DOI 10.1109/LICS.1996.561463:
  https://lics.siglog.org/archive/1996/Narendran-Solvinglinearequati.html
- Author-associated copy linked by the University at Albany faculty page:
  https://www.academia.edu/108178336/Solving_linear_equations_over_polynomial_semirings
  The accessible transcription has damaged two-column/formula ordering; the
  original PDF was not visually verified in this continuation. Doczz returned
  410, CiteSeer PDF returned 403, and DOI opening was unavailable.
- Dong's primary published STACS 2023 PDF, pp.26:1–26:2:
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol254-stacs2023/LIPIcs.STACS.2023.26/LIPIcs.STACS.2023.26.pdf
  It confirms fixed integer-polynomial coefficients and shared N[X] unknowns.
  Dong's decidable single homogeneous equation with all unknowns nonzero is
  a different problem and is not used as this undecidability supplier.

The accepted Narendran targets/proofs already establish:
- SquareGadget(u,v) iff 2v+u=u^2, not v=u^2; zero values included.
- ConstantGadget(v) iff v=C(2^k-1).
- SimultaneousConstantGadget forces an arbitrary finite family to be natural
  constants, allowing zeros and the empty family through one sum-with-slack row.

For a circuit with n inputs and g gates the archived allocation has scalar
block S=2n+5g. Original wires occupy [0,n+g), input slack [n+g,2n+g), and four
scalar reserves per gate [2n+g,S). Twelve geometric-polynomial reserves per
gate follow in [S,S+12g), then nine global constant-gadget wires. The global
constant forcing ranges only over indices below S, never geometric witnesses.

Multiplication is represented by s=x+y and T(s)=T(x)+T(y)+out, with three
triangular gadgets. Their identities force out=xy. The input rows y=slack+1
match positive circuit inputs only after the proved shift P(Y-1) is applied.

The eventual total H10 adapter must check ORIGINAL polynomial decoding and
well-formedness before shifting/compiling. Counterexample to omitting that
check: inputCount=0, monomials=[(1,[0])] is invalid, but shifting to X0-1 and
compiling can alias out-of-range input zero to the initial constant-one gate,
producing a well-formed circuit with equal outputs 2. Testing only compiled
circuit/system well-formedness does not reject that source instance.
Decode/WF failures should map to a fixed well-formed unsatisfiable system,
for example zero unknowns with the single constant row 1=0.

NumericCircuitEncoder specifies canonical circuit encodings only. The final
adapter owns malformed-input rejection. systemOfCode uses filterMap, so a
separate WF conjunct/no-reference-loss theorem is required for raw row meaning.

The current CircuitBridge gate covers only exact row meaning, shared-system
semantics under WF, and allocation WF. FullCircuitEncoding, NumericCircuitEncoder
and CodedH10ToLinearSystems remain pending.
