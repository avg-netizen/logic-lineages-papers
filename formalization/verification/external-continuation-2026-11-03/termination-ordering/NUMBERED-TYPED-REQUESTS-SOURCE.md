# Actual one-layer typed decoder requests

Paper06 lines551–556 requires effective typed syntax. This component defines first-order requests for the existing mutual term/argument decoder and an executable one-layer expander. It preserves exact local variable-index/type checks, literal native head signatures, lambda binder extension, function-before-argument order and ordered base/extras or head/tail child lists.

The two targets prove actual decoder success equals expansion failure false or conjunction of actual decoder success on every emitted child. No child-success oracle or semantic supplier is assumed: the right side calls the existing decoder directly. No accepted implementation is changed.

This is one-layer correspondence only. Global worklist termination/fuel, primitive recursion of request expansion/evaluation, dependent output coding, full checker effectivity, arithmetic representability and well-foundedness remain separate.
