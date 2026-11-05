# Ordinary minimization graph closure

Target-only preflight: 1793878153837987064-2. First proof gate:
1793878273189897283-2. All three exact aliases passed, each with only propext,
Classical.choice and Quot.sound. The 56-module local import closure matches
successful source-bound native receipts. Parent review/adoption pending.

The specification is the actual Mathlib Code.rfind' evaluation. It returns
an absolute index y = t + start, evaluates the body to zero at offset t, and
requires an actual defined nonzero output at every offset i < t. An undefined
earlier computation cannot be skipped. Start and offset may both be zero.

The Diophantine proof constructs the earlier-offset existential output graph,
uses the checked original variable-bounded universal closure, intersects with
the zero-output graph, and transports the input through the actual Nat.unpair.
No termination hypothesis or replacement evaluator is introduced.

Source correspondence is directly to pinned Mathlib PartrecCode.eval and
Partrec.mem_rfind. This pays one actual ordinary-code constructor. Primitive
recursion, full code induction, universal evaluation, effective fixed-polynomial
specialization, RE reduction and undecidability remain separate unpaid steps.
No source-register promotion is asserted.
