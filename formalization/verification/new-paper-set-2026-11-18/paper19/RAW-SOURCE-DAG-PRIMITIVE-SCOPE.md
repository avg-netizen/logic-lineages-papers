# Raw numeric validator primitive checkpoint

Requested bounded root: LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorPrimitiveProof.

Imports only the new concrete RawValidatorDefinitions plus the existing raw codec definitions/type-code primitive library. This candidate proves primitive recursiveness of the numeric bounded variable/spec lookup, all seven literal tag and exact arity checks, tail-first graph fold with cumulative validity, and final root/type/prefix checker. It does not import or claim the still-unproved checker/typed-decoder equivalence.

The state is a pair (literal newest-first specification list, cumulative validity Bool). Even an invalid tail retains its raw specification list; the validity component is conjoined at each node and at the final root, so later successful local checks cannot repair an invalid tail. Actual graph reconstruction is not replaced by this numeric state.

Lookup requires index < length as well as equality of getD; default values cannot accept out-of-range indices. Type codes use the existing bijection, with literal arrow/case/recursor codes. All seven constructors and exact payload lengths are present, including actual tag 5 case.

The bounded result is only Primrec RawValidator.check, not Computable frozen valid or reifyCode. Those require the separate operational equivalence proof against the actual dependent decoder and the already-compiled successful decode/encode converse. All original six frozen pins remain unchanged. No full codec or compiler promotion from this checkpoint.
