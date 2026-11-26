# Paper16 actual type, head and finite binder-stack numeric codes

Source: foundations.tex 3–18 and 36–53 for the actual simple type
and distinct native/typed-app/ranked heads; ordinals.tex 13–29,
69–84 for a single represented finite-context typed numerical
universe and actual arithmetic witnesses. This preparatory
packet chooses explicit natural codes. The source does not
prescribe a numerical coding convention.

- **Literal type AST.** The ground code is zero; each actual original
  arrow is a positive pair of its actual domain and codomain codes,
  retaining orientation. The natural fuel is the code itself, not a
  supplied depth oracle. Calibration pays soundness of every parsed
  result, arbitrary sufficient-fuel completeness, exact successful
  decoding and roundtrip, and exact malformed rejection.
- **Literal distinct head constructors.** Separate tags for zero,
  successor, case, recursor, typed original application and ranked.
  Zero/successor require empty payload (numeric zero); case and
  recursor retain the full result parameter; actual original app
  retains both domain and codomain. Ranked retain the actual pair
  of nominal name and declared arity. No head identification by
  precedent rank or replacement of the original numbered output
  type. Original head admission/signature guards remain separate.
- **Actual finite binder stack.** The nearest-first List Ty is
  preserved literally as nested positive pairs ending at zero;
  recursively decoded type annotations are retained. Decoding
  failure is exact as for other codecs. Coded lookup is ordinary
  optional list lookup after decoding this concrete natural input.
  It equals the actual existing BoundContext.prefix Γ EmptyContext
  at every index, including absent entries. This is not generic
  arbitrary-function C coding; actual free names remain globally
  typed pairs, not additional binder slots.
- **No stronger arithmetic inference.** Uses packet448 polynomial
  exact pairing/inverse as a concrete dependency. This does not
  yet code NTerm/NArgs, arbitrary paths/certificates, choose a least
  primary class representative, prove primitive-recursive source
  compiler or object-language arithmetic/ID1 accessibility.
  Existing source, syntax, finite binder proof and accepted files
  are unchanged.
