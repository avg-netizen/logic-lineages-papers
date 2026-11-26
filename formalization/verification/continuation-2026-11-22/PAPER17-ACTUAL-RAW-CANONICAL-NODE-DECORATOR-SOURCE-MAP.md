# Paper 17: exact executable partial mask decoration of the canonical ordered tape

Printed source: `arithmetic.tex`, actual full-value comparison pattern
and choice of maximal class in signed order normalization.

- Process the same literal raw canonical grouped ordered tape one
  occurrence at a time. Only a genuine syntactic active-label slot
  consumes a supplied Boolean; inactive terms receive false without
  consuming a bit. The code uses an optional head, never a default
  bit. Reject early exhaustion and excess bits; on success return
  the same original tape with bits in that exact order.
- Primitive recursion over the tape stores only a remaining mask
  and reversed output accumulator, reversing at the accepted end.
  On literal input, prove calibration to the existing typed partial
  decorator, its exact mask length domain and row/order retention.
- Use the checked canonical grouped encoder and the literal
  supplied-answer class flags to compose the same typed/raw
  interface on original inputs. This does not check real reads,
  comparison truth, or correctness of supplied external answers.
  No coefficient, successor, trace, high route, whole solver,
  or numbered promotion.
