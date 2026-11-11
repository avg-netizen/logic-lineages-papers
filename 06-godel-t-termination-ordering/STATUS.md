# Mathematical status

The transitivity and stable-pair claim in this working manuscript requires
source correction or a proved change of interpretation. The current literal
Lean relation has a checked counterexample even on closed ordinary terms over
a four-symbol ranked signature, with strict-total well-founded precedence and
the stated type-support confinement.

Use `Z < H < K < F`, of arities `0, 0, 1, 2`, and set

```
P = (lambda x. F(x,Z)) K(H)
T = F(K(H),Z)
U = F(H,H).
```

The checked relation has `P Weak T` and `T Strict U`, but no `P Weak U`.
The negative result excludes every finite derivation by induction; it is not
a bounded search failure. The local stable-pair claim therefore cannot be completed
by another proof lemma for the unchanged relation.

The [finite-signature evidence](../formalization/verification/local-resume-2026-11-02/termination-ordering/FiniteOrdinaryBetaDiagnostic-ACCEPTED.json),
[full diagnostic](../formalization/verification/local-resume-2026-11-02/termination-ordering/ORDINARY-TRANSITIVITY-DIAGNOSTIC.md)
and [repair boundary](../formalization/verification/local-resume-2026-11-02/termination-ordering/STRICT-MARK-REPAIR-BOUNDARY.md)
are included in this repository. They retain the literal original marking,
application and multiset rules. No repair by transitive closure or repeated
marking is silently substituted into existing theorems.

This is a result about the local specified relation. Correspondence with the
scope and conventions of Kop's published strong-pair theorem remains a
separate obligation; no error in that published theorem has been established.
The existing local fixed-point adequacy, decision procedure and ranked-RPO
restriction have checked exact statements. Full well-foundedness, arithmetic
accessibility and ordinal-height conclusions remain unproved here, rather
than refuted by this counterexample.

The manuscript source and PDF have not been silently rewritten. Read them
with this status qualification; the full stable ordering and height package
is not currently established.

The [11 November repaired proof checkpoint](../formalization/verification/fable-collaboration-2026-11-11/STATUS.md)
checks 33 supporting rank, transparent-minimum and activated-observer contracts
under the original specifications. It also checks native all-input calibration
of the activated rank guard. These results do not establish the original
context-uniform internal accessibility derivation or resolve the transitivity
obstruction above. The numbered register is unchanged and proof work is paused.
