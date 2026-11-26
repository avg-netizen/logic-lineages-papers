# Actual equality syntax validator: accepted exact1

Frozen InternalValidator passes exact gate and standard-axiom audit:
receipt1794604583205068932-5. The only installation premises are the actual
equality quotation AST and formulaValidator AST in the same registry.
Scanner/pair/cons/equality helper nodes come from the validator AST; append
comes from the quotation AST. Internal scan at empty rest and the actual
validator completeness derivation yield result1 for arbitrary symbolic runtime
values and binder context. No separate syntax assumption or native reflection.

This result is formula-syntax acceptance, NOT truth of quoted equality,
acceptance of a proof certificate, computation quotation, HB3 or numbered
completion. Final source-selection integration remains a separate obligation.
