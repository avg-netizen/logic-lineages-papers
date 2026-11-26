# Raw source DAG codec final review handoff

Full gate: LogicLineages.ControlSensitivityCurrent.RawSourceDAGStatementChecks.
Ticket RAWSOURCEDAGFULL-1716, receipt 1795022182535662698-5, passed/reaped/released.
Recursive evidence: RAW-SOURCE-DAG-EVIDENCE.json, 137 source-matched modules, no errors, four standard-only original aliases.
Frozen comparator: RAW-SOURCE-DAG-FROZEN-PINS.json, six unchanged pins.

Proof sequence: RawSourceDAGRoundtripProof; RawSourceDAGValidationProof; RawSourceDAGRawValidatorDefinitions; RawSourceDAGRawValidatorPrimitiveProof; RawSourceDAGRawValidatorLookupProof; RawSourceDAGRawValidatorEquivalenceProof; RawSourceDAGEffectiveProof; RawSourceDAGStatementChecks.

The actual dependent decoder reconstructs all seven typed source-DAG constructors plus nil, retains repeated/unused vertices and literal root indices. Successful reconstruction re-encodes the exact raw graph; invalid syntax returns none. Numeric checker explicitly validates payload arity, finite reference bounds, local prefixes and type codes, with a tail-first fold preserving cumulative invalidity. Proved operational equality transports actual primitive-recursive checker computation to the frozen valid function; actual decode/encode converse transports computation to the frozen reifyCode. There is no choice-based decoder or expanded-tree proxy.

Failed editions and receipts are preserved in raw-source-dag-roundtrip-draft01..06, raw-source-dag-validation-draft01, raw-source-dag-primitive-draft01..02, raw-source-dag-lookup-draft01, raw-source-dag-equivalence-draft01..02. The helper reserved identifier quoting repair was independently approved and confirmed; it did not touch frozen definitions/targets. All gates retained original caps and upstream-cache-only policy.

Supporting codec only. Whole input/gate/operation compiler raw reconstruction and joint computability, plus eventual complete numbered compiler assembly, remain separate.
