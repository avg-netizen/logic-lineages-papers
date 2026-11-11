# Original constructor computability: frozen endpoints

Source: `06-godel-t-termination-ordering/paper.tex`, lines 605–619, with the original strict-total finite constructor precedence at lines 79–83. The native proof must follow head class, base multiset, finite label then omega, and extra multiset, in that order.

The numbered target literally retains every hypothesis of `SourceZeroNumberedComputabilityTargets.ActualZeroNumberedComputable` at the same n, arity, Gamma, encoded context, decoded ctx, and scalar. The only changes are an arbitrary finite label k in place of 0 and a rank function `Fin n → Fin n` satisfying `rankCertificateTest ctx.2 rank = true`. The ordinary companion has the same context/calibration/rank hypotheses, an actual ordinary constructor in the finite universe, and computability of each literal base member. Its conclusion is actual computability at the head's result type.

Neither target assumes constructor closure, whole-constructor accessibility, successor closure, or computability of reducts. Neither uses observer soundness as the actual logical relation. Primary permutations must retain separate base and extra measures; all induction hypotheses must remain universal over equivalent heads, result types, and later parameters. The abstraction branch uses the native unrestricted lambda theorem and opened-numbered beta identity at the original Gamma, not a calibration in an extended context.

Status: targets authored and frozen before candidate proof authoring; preflight and proofs pending the coordinator's serialized native gates. No compiler or Git command was run by this worker.
