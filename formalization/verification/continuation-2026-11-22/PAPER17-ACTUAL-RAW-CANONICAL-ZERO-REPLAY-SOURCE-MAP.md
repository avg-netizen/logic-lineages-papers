# Paper 17: executable replay of supplied canonical zero comparison tapes

Printed source: `arithmetic.tex`, the finite inner signed
normalization loop along a supplied comparison path.

- Start from the exact encoded original signed syntax. For each
  supplied finite comparison tape use the existing own-order raw
  canonical grouping and zero-node body, keep the actual encoded
  constant and ordered terms, and propagate absence of a successor.
  Empty supplied path returns the initial state. This is a
  syntax-only program: it neither derives nor inserts any read flag.
- PR folding of the exact checked one-node syntax operation
  calibrates to the typed canonical replay on the same sequence of
  encoded answers. No enumeration or assertion of comparison truth.
- Separately, when the original typed CanonicalTrace premise is
  supplied (exact matched actual ordered comparisons, readiness
  and attached actual zero witnesses), recover exactly the encoded
  erased final typed state. No derivation of this premise or proof
  of progress, termination, terminal sign, high routes or solver.
