# Actual typed focus and context replacement

The contextual numeric step checker for paper06's numbered reduction calls
`NumberedTypedFocus.focus`, decodes a replacement at the discovered binder
context and type, and reconstructs the outer term using the original
`NumberedStepContexts.plug`. This component exposes primitive computations of
that focus and reconstruction while keeping the original typed functions as
the comparison targets.

`focusCode path Gamma tau code` returns exactly the hole context, hole type
and selected term code on every genuine typed source. Its calibration is an
equality of `Option` values, so failed paths and indices remain failures.
The permitted positions are exactly lambda body, auxiliary application
function, ordinary base index, numbered base index, and numbered extra index.
There is no auxiliary application argument position.

Lambda descent checks the raw expected arrow/domain agreement and prepends
the lambda domain to the context. Function descent retains the outer context
and uses the original function type. Indexed descent reuses the accepted
strict argument-entry extractor and the original zero-based list index,
including duplicate entries and out-of-range rejection. No original source
codec, path codec, typedness checker or argument extractor is re-proved here.

The trace retains each position together with its original source root, in
order from the hole outward. `replaceCode path Gamma tau code replacement`
reassembles that trace. Each argument replacement retains its original type
and all other entries in order. Every lambda domain, application argument,
head, finite label, explicit result, extra-type list and untouched base or
extra list is preserved. No variable shifting or renaming occurs: the typed
calibration supplies the replacement at the actual discovered `holeGamma`
and `holeType`, exactly as the original dependent `plug` requires.

The structural trace recursion has a primitive path-fold implementation;
reassembly is a primitive fold over its frames. The five frozen targets are
exact focus calibration, typed replacement calibration, replacement failure
on every invalid original path, joint primitive-recursive focus, and joint
primitive-recursive replacement. Both computational targets vary the path,
context, expected type and all source/replacement codes. The raw functions
need no arity argument; their comparisons quantify every actual finite
signature, arity, context, result type and typed source.

These raw functions do not replace the original typed decoder. An arbitrary
raw source need not be well typed; its numeric validity remains the outer
decoder's responsibility. The exact typed comparisons and failure target
preserve the behavior needed by the unchanged numeric step checker without
adding a source-universe guard to its internal selector. Context-uniform
selector/decoder computation, complete numeric step integration, quotient
edges and positive paths remain separate obligations.
