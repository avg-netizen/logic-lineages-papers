# Paper16 literal NTerm/NArgs natural numeric codec

Source: foundations.tex 3–28, 36–53 and ordinals.tex 13–67, 69–84.
The source requires an actual arithmetic carrier and numerical
witnesses but does not demand a particular coding convention.
This is the exact Nat codec of the existing actual raw annotated
syntax, not yet a coded typing/step/path relation, least-class code,
primitive-recursive program/formula reflection or internal ID1 proof.

- **Exact literal arrays and tags.** Field lists are ordered nested
  positive pairs ending at zero. Numeric constructor tags and ordered
  field lists are a distinct positive pair. All constituent fields
  lie strictly below the enclosing list/node code; this bound and
  actual numeric fuel correctness must be proved, not provided as
  a depth oracle. Exact successful decoding, roundtrip and
  malformed rejection are target contracts.
- **Every actual original NTerm field.** Globally typed free (type,
  Nat name) and de Bruijn bound (type,index) have different tags.
  Lambda preserves its actual domain and body. Bottom retains its
  type. Ordinary heads preserve the full literal original head
  code plus its actual ordered base list; numbered retain the
  full original head, actual current output type, finite natural
  label, and separate ordered base and extras. The original head's
  own full declaration parameters are not collapsed into current
  output. Auxiliary application retains its two actual annotations
  and ordered function and argument, distinct from original
  literal Head.app or an ordinary equal head-rank test.
- **Actual NArgs.** Nil and cons use zero/positive pair, storing each
  full term and remainder, with no permutation, omitted instances or
  code normalization. Successful decode must recover literally
  the exact AST or literal NArgs; unsupported tags/wrong arities
  are rejected. Atomic type/head decoders are the actual packet449
  codecs and there is no additional assumed recursion/correctness oracle.
- **Whole numeric carrier only at later bridge.** The intended
  later carrier combines these codes with the previous concrete
  finite binder-stack code, genuine fixed scope and checked typing
  bit. This codec itself admits every existing raw AST, including
  untyped syntactic candidates; no inference of typing on parsed
  values. No arbitrary functional context C coding, arithmetic
  ClassEdge/RS, least primary representative or ID1 result.
