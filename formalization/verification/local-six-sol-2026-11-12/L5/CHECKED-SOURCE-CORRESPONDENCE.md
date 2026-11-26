# Checked source08 arithmetic supplier correspondence

The source is 08-multivariate-collapse-comparison/paper.tex, thm:snyatkov,
lines156ff: the complete first-order theory (Nat;0,1,+,<,f) is decidable.
The exact control at eq:f, lines95ff, has variable starting argument
F0(n)=2^n, F(j+1)(n)=Fj^(n+1)(n), f(n)=F5(n+100).
Source SHA256: a4a8481437b8c7683ee8d82ec9e13e0a29af44110edcace0e9b0ef31b8fdaf0d.

The checked declaration is
LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionStatementChecks.fullSourceDecision,
with exact frozen type SourceDecisionTargets.FullSourceDecision in
SourceDecisionWorkingTargets.lean. It states that an actual Nat-to-Bool decision
function is Computable and, for every original closed SourceFormula and every
original valuation, returns true exactly when the original formula is true.
Only the syntactic closed-sentence condition is required.

Original SourceFormula is the unchanged ContractDefinitions syntax: arbitrary
source equal/less atoms, negation, conjunction and existential natural binders.
These form the complete first-order grammar, with universal quantification and
other Boolean connectives expressible by their usual logical combinations.
Original BaseTerm has natural numerals, raw names, addition and arbitrarily
nested Phi. Its value function uses the same ControlDefinitions.Phi as the
manuscript. No bound-dependent/nonlinear term, alternation or shared-name
correlation is excluded. Function.update retains the original named binder and
shadowing semantics.

The source program is not chosen from a semantic existence statement. It is the
explicit SourceDecision.answer = groundMatrix ∘ eliminate, whose total numeric
Computable proof is checked. LiteralTermEmbedding, LiteralBinderCompiler and
LiteralSourceCompiler calibrate each exact stage to the original concrete
OriginalSourceElimination algorithm. Its accepted actualSourceElimination has
all original formulas/valuations and no solver/effectivity/source-shape premise.
Its originalSourceNameSupport removes free-name concerns for closed sentences.
The new ground evaluator is proved against actual Term.value and Matrix.eval,
retaining the real Phi, fixed-seed H, inverse defaults, zero division and zero
modulus semantics. H is the separate actual auxiliary H0=1, H(n+1)=Phi(Hn);
it does not replace the source's variable-seed F5 hierarchy.

BUILD-014 checked all nine exact source gate aliases with only the three allowed
foundations. BUILD-012 separately checked the six-declaration Boolean compiler
bridge. Frozen targets and checked source bytes are unchanged. The full-source
target and proof contain no extra class field, axiom, oracle or unresolved
supplier premise. No broader auxiliary-H language QE claim is made.

Root alone decides numbered adoption and downstream common-head/balanced
assembly. The lane's own register/manuscript/Git state is unchanged.
