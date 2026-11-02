# Structural semantics: scope qualification and fixed-point path

The checked paired evaluator is an actual executable mutual recursion on unchanged confined marked syntax. Its monotonicity, world restriction, empty-scan law and all branch equations remain valid. Its confinement is exactly the type/head projection of the established finite query Frame. These are checked mathematical interfaces; identification with every clause of the manuscript's structural interpretation remains pending. In particular, no whole `lem:structural` promotion is justified.

## The unresolved cross-type equation

The implemented marked evaluation at a family M is its actual row M(f, σ, P, a). Scanning that original marked head with a complete nonempty suffix s and tuple v appends all supplied values and returns

    M(f, result(s), P, appendInput(a, packTuple(σ, s, v))).

To identify this with applying the evaluated marked value requires the precise equation

    applyValue(M(f, σ, P, a), s, v)
      = M(f, result(s), P, appendInput(a, packTuple(σ, s, v))).

Here σ and result(s) carry their actual source type membership, and appendInput uses the real downward closure. This equation is not among the defining hypotheses of a generic coherent constructor family: those hypotheses are input monotonicity and observation-world restriction coherence. The previously proved generic paired-action results do not assert it.

The actual source operator supplies instead the stage-indexed equation

    applyValue(F(M)(f, σ, P, a), s, v)
      = M(f, result(s), P, appendInput(a, packTuple(σ, s, v))).

Consequently replacing every marked evaluation by F(M) alone would not establish the desired same-family identity: the syntactic result would then be interpreted at F(M), whereas this table consults M. No silent strengthening of the constructor carrier or change to the original target is permitted.

## Independently available discharge at the actual solution

At a genuine fixed point F(M)=M, the two equations coincide by equality substitution. The already constructed finite limit is proved to be an actual fixed point of this specific source operator, without a new consistency assumption. Thus the next sound route is to derive the exact complete-tuple identity for that actual limit, then prove the source application/substitution correspondences with their literal syntax and existing confinement closure. This is a fixed-point interpretation route, not a proof of the manuscript's stronger arbitrary-family structural statement.

The source availability/strict-bit equations can likewise be read from F at its actual fixed point. Stagewise reasoning, if used, must retain the explicit successor/current-stage distinction rather than asserting same-stage application exactness.

No concrete counterexample in an actual finite input universe is claimed here. The absence of the needed equation from the generic hypotheses is a proof obligation and a semantic identification concern, not by itself a formal disproof. Any later counterexample must provide actual typed domain values, valid worlds, constructor coherence, and a genuine inequality in that same universe.

Frozen definitions, targets, proofs and prior receipts are unchanged. This separate qualification accompanies the current scoped assembly result; substitution, simultaneous special-application correctness, adequacy and a full structural source claim remain pending.
