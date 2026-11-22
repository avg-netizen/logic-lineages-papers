# Paper 17: finite executable prefixes of canonical structural zero paths

Printed source: `arithmetic.tex`, finite signed
inner normalization along candidate comparison branches.

- At each exact breadth level, extend each original raw candidate
  by every literal submitted answer tape of that state's own
  canonical ordered label-pair width. Keep only structurally
  successful original raw zero-step syntax, and retain its exact
  submitted tape and output state. Empty level/path is included.
- The stage-bound input here is explicit fuel. Prefix enumeration
  is exactly the candidates with zero-path relation and tape
  count at most the supplied fuel; each emitted tape successfully
  replays to precisely its returned raw state. Conversely supplied
  paths with the exact generated next-node widths and successful
  recorded edges occur. No deduplication, read, or truth test.
- Primitive recursion over the supplied finite fuel, moving a
  concrete candidate list rather than a higher-type function.
  This does not derive the fuel, prove any supplied tape is
  true, compile guards, choose terminal signs, complete high
  routes or claim the closed theorem.
