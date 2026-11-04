# Uniform finite leaves of the existing Plan compiler

This supporting obligation supplies the explicit finite-leaf premise needed by the already checked Gamma conjunction aggregator for paper09. It uses unchanged ExistentialPlan.compile and actual source DAG terms, with successful default-policy assignments and finite raw ordinal values, not a fallback scalar.

UniformFinite is structural: done is true; a supplied equation requires both source DAG leaves finite at every ground valuation of its own context and recurses; a gate only recurses; an existential ground binder requires the body condition at every body valuation. It assumes neither equation truth nor existence of a satisfying valuation. Inputs retain the existing convention: ground components rho, unused functional natural components zero, with all raw ordinals raised by one.

GeneratedLeaves proves all emitted primitive leaves finite at every arbitrary valuation of the actual nine-coordinate Block. This includes all gate constructors as a syntactic finiteness claim only; no sort correctness or semantic transfer is asserted. Generic control assumptions are exactly StrictMono G and n <= G n. The exact primitive calibration already proves finite values for every Expr used by lower.

UniformCompiler quantifies every final valuation independently. There is no Eval, Holds, Supported, canonical-witness, or prescribed original-input-extension premise. The equation branch pulls valuations back along the actual embedding; the gate branch uses literal generated Expr calibration and shift-nine Scalar transport for inherited leaves; an existential binder does not change the compiled forest. Gamma specialization exposes exactly SourceGammaAggregate.FiniteLeaves on the actual mapped terms.

This does not establish UniformFinite for the halting Plan, arbitrary-source finiteness, a universal/weak comparison, numeric encoding, complexity, or hardness. The halting Plan instantiation remains a separate obligation. No accepted source, manuscript or register changes. Proof candidates remain absent pending exact review and prospective freeze.
