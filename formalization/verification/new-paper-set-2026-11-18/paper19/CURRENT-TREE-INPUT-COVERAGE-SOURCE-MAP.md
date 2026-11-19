# Literal original tree to current shared-input coverage (supporting)

Paper19 uses unnormalized original typed source terms (setting.tex 32–45),
and treats supplied source leaves as scoped source DAGs (compiler.tex
126–136). Its full all-ground-free-variable comparison domain, including
all finite result types, is printed in observers.tex 37–51. That domain may
not be shrunk to a convenient image of a compiler. The existing current
`CurrentTreeCode.expand` has checked DAG→original-tree calibration. This
packet supplies the reverse exact coverage using the actual current
`GroundEquivalence.Input`/raw DAG type and immutable
`SyntaxCode.encodeTerm`/raw original checker. It is not a numbered decision
equivalence on its own. It does not change the owner's eight frozen
CurrentDecision pins.

- **Typed finite source occurrences:** produce one new vertex per original
  source constructor. Each scope is the unchanged binder prefix Δ and
  unchanged free context Γ; occurrence variables are exactly the same
  typed de Bruijn identities. An application is built as function then
  argument then literal application, with both references prior to the
  resulting vertex. A lambda adds the domain to Δ and then points to
  its actual scoped body. The four native constants have their original
  types and tags. New vertices need no sharing; every genuine finite tree
  is included, even if an equivalent compact DAG also exists. The builder
  retains every reference to an old graph row when adding a new root.
- **Literal raw coverage:** original raw tree tags 0–6 correspond to
  var, zero, succ, case, recursor, app and lambda. The existing Context/
  SyntaxCode checker itself computes result/domain type tags and controls
  rejection of malformed top-level inputs. Application emits the
  application row followed by argument and function rows; the original
  function-root reference is shifted by exactly the number of argument
  rows and the most recent argument root is reference zero. Lambda emits
  its actual node before the body rows, with original type/prefix and
  body reference zero. Establish the general typed table-append/readout
  shape and exact earlier-reference index shift by the number of new rows;
  combine with typed checker calibration on exactly the same source to
  prove literal typed code equality. The existing reverse expansion then
  yields the original unchanged radix-eight tree code, not a semantically
  equivalent tree chosen afterward.
- **Program totality:** the numeric table recurses only on strict numeric
  subcodes. Show actual child selector and output assembler computable
  with fixed scalar arithmetic, finite list/append operations and the
  already proved raw type checker, then apply the checked finite decreasing
  graph computation with measure equal to original code. The outer program
  wraps the resulting table under the original typecheck response. The
  resulting `Computable₂` is on all raw input codes; semantics and literal
  calibration are on the genuine typed source encodings. A malformed
  code with check = none is rejected, not mapped to a valid restricted
  comparison.
- **No semantic substitution:** no canonical assignment, condition on f/p,
  bound on original result type, closedness of a source, fixed level,
  assignment of functional units, or restriction to ground free name
  contexts is used to obtain coverage. Taking the well-typed ground
  contexts specializes this supplier to the exact numbered source.

Require target-only preflight including the separately frozen constructive
definitions, independent scope before proof, actual authored review and
original fixed serialized Mathlib profile, exact named standard-library
axiom evidence, fresh recursive source/object/log/receipt reconciliation,
and independent final. Preserve failed editions; frozen changes only
after proposed/applied independent reviews.
