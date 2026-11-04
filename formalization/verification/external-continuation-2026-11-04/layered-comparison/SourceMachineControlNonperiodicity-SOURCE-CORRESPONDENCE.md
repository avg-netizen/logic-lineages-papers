# Actual machine-clock perturbation parity

Paper09 hardness.tex lines233–240 fixes a primitive-recursive blank-program test H and defines Gamma_b by adding H(v2(n),n) above b to fixed Phi. Lines321–333 establish non-eventual-periodicity of its parity.

The explicit chosen enumeration here is the accepted numerical finite-table TM0 model. SourceBlankMachineSimulation proves H(e,t) tests termination in at most t actual transitions using simulation fuel t+1 (the extra unit observes halt). SourceBlankHaltingReduction proves this exact enumeration's blank-halting predicate undecidable by a primitive-recursive compiler reduction. This component does not equate the machine clock to Code.evaln stages.

ExactControlParity proves primitive recursion of this literal Gamma_b and its parity above b for every finite b. It reuses the fixed Phi evenness and existing perturbation code.

NonEventualPeriodicity proves for every b there are no N and positive p satisfying parity repetition for all n≥N. Reuse the accepted explicit valuation fibers n_e+k p 2^(e+1), their primitive recursion, bounds and exact valuations. A hypothetical period makes the actual machine test along every fiber constant; monotonicity and eventual-halting equivalence yield a computable decision of actual blank-table halting, contradicting the accepted reduction. No period-finding algorithm or oracle is postulated.

This realizes the manuscript nonperiodicity argument for one explicit effective machine enumeration. The manuscript does not fix a particular machine syntax, so no intended enumeration identity is inferred. The full control-hardness theorem, canonical source conjunction construction and reduction/membership clauses remain separate. No whole-source register promotion is requested.
