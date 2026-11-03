# Literal ordinary context closure — reconstructed contract

Source: paper06 `lem:context` (Explicit application contexts): if ordinary
s strictly compares to t, replacing s by t in any ordinary context yields
another strict comparison. Source proof uses actual Stat at literal typed
application heads, a strict matched occurrence, Select for whole-source
argument premises, and lambda closure. It does not invoke an unproved
strong-pair theorem.

Context is an ordinary typed one-hole syntax tree, with the hole's local
ambient context and result type explicitly indexed. The five constructors
cover hole, application-function, application-argument, lambda, and each
ranked argument position. The plug operation constructs source syntax: no
reduction, normalization, beta quotient, or semantic substitute. Lambda
frames track local binders, so open and binder-local ordinary holes are
covered rather than just closed inputs. The named version uses the existing
lookup/shadowing syntax and literal erasure, not a new parsing oracle.

The ten exact targets include actual generalized strict-multiset promotion
from aligned weak matches with one strict occurrence, zero-argument original
Select, ordinary-head and lambda strict congruence, full ordinary context
strict closure, exact source typeSupport monotonicity and confined closure,
literal named-context erasure, and full named strict/confined closure.
Support remains actual subterm/binder subtype support; unused ambient types
are not inserted. No extra strictness premise on untouched arguments is used:
ordinary weak reflexivity supplies them. No arbitrary marked-context closure
is claimed; the original endpoints and context are ordinary.

The full ordinary/named strict context targets cover the numbered context
lemma, subject to final source review after independent acceptance. The
helper targets alone are not whole-lemma completion. Confinement and named
calibration are additional exact source interfaces. This does not prove
transitivity, substitution stability, well-foundedness, or the full stable
pair. Prior lost acceptance is not evidence: this component requires fresh
comparator, prospective freeze, proof, gate, independent audit and verified
remote publication before another component begins.
