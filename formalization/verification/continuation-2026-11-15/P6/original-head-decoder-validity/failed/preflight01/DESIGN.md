# Original head-decoder validity: exact2 freeze

## Existing guard inventory and source correspondence
The original NumberedNumericDecoding.headParse/decodeHeadNumber accepts tags 0/1 only with zero payload; tags 2/3 decode a type; tag 4 decodes a pair of types; tag 5 requires payload<n; all other tags fail. NumberedTypeCodecTotalTargets/NumberedTypeCodecPrimrecSupportProof already supply total original type decoding. The filter in decodeHeadNumber still requires an explicit parser-soundness/round-trip justification; it is not discarded by definition.

Search across OriginalHead* and global source-computability definitions found no explicit Program implementing this all-raw syntactic guard. Existing OriginalHeadEncodingBridge.encodeHead calibrates only valid head numbers and does not reject all malformed payloads. Existing OriginalHeadWindow.window tests source type/symbol windows, accepts malformed basic payloads and is not decoder validity. Existing OriginalHeadClass is also not validity. No existing guard is silently relabeled or changed.

The new finite AST reuses OriginalHeadEncodingBridge.choose, original equalityTest and ltTest, actual unpair-right, and constant nodes. n is a fixed finite symbol bound, not an arity oracle. NativeDecoderValidity compares every raw value directly to the literal original decodeHeadNumber. InternalAcceptedBranches characterizes actual graph(check n)=1 using original pairing observations and object-language equality/order/disjunction; arbitrary tag/payload, no native correctness premise.

## Plan
First prove all-raw native calibration, using total original type codecs and parser soundness. Then prove internal branch acceptance/constant rejection using actual choose/equality/less-than graph equations; split the six tags and unknown residual internally. All selector values and comparison witnesses must be derived from the actual pairing observation. Frozen allowed formula and AST remain fixed. Independent review and preflight precede proof; coordinator alone compiles/publishes.

## Unpaid boundaries
This is not HeadInWindow, typed acceptance, full recursive code validity, the decoded/default[] dependency supplier, selected supplier installation, or E completion. Next recursive code guard still has to validate all code constructor tags, argument-nil zero payload, recursive child validity and these head obligations. Conversion of encoded Node to raw fields, all-input guarded supplier calibration including invalid nodes, and internal installed recursion laws remain unpaid. NumericDependencyCross FULL04 passed native exact3; its independent evidence audit was pending when this target was frozen.
