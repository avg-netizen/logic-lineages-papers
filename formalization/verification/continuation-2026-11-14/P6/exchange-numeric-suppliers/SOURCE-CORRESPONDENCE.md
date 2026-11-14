# Concrete numeric original-exchange suppliers, exact4
Source: NumberedExchangeCodePrimrecProof.codeExchangePrimitive and layerCalibration.
The original typed algorithm uses beta = Code-pair, window = symbol/type lists;
rank is codeNumber of source; dependency list is the literal original cross;
optional layer is SOME(layer original fields, recursive Bool answers).
These definitions explicitly extend those typed functions to numeric node/window
codes. They do NOT assert that arbitrary malformed Nat inputs were already part
of the original typed algorithm.

decode is the actual Encodable.decode for Node/Window. Invalid node: rank0,
empty dependencies, value0, layer Some0. Invalid window: value0 and layer Some0,
but node rank/dependencies are unchanged (as in the window-independent originals).
False Bool is numeric0, and its optional answer is Some0 (encoding successor0),
never None. Arbitrary numeric answers use exact-one conversion; valid original
Bool outputs recover exactly. The unchanged original layer handles short answer
lists with getD0/getD3 false. layerValue uses actual decodeNumbers/getD[] for the
numeric list input; no raw-list reencoding assumption is hidden.

NativeRankDecrease and NativeLayerLaw pay the previously explicit ALL-numeric
coherence hypotheses. NativeOriginalValue connects the extension on valid encoded
nodes/windows to exact original codeExchange. NativePrimitiveSuppliers constructs
Primrec proofs only, using original rank/dependencies/layer primitives, not the
entire codeExchange to compute the layer. valueAt may only serve the specification.

Still unpaid: selecting the Program witnesses, concrete recursion/extraction and
packed/context wrapper installation; internally connecting suppliers and the
transparent 19-field layer; semantic internal E/coverage/headMove/class coherence.
No selected E replacement or full tuple change is claimed. No native reflection.
