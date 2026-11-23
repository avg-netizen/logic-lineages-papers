# Paper 16: literal nested odd induction, conditional J union

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
lines 84–98 define I and J in one original tagged body.
Lines 142–148 call for nested J induction and a genuine origin-labelled
certificate split. This packet closes the two logical inductions only,
conditional on the arithmetic suppliers below.

* [Outer syntax](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedUnionOuterSyntaxProof.lean):
  the literal outer motive is `J(a) ∧ ∀ b (J(b)→∀u(U(a,b,u)→J(u)))`.
  Here U is the original #1519 packed parser/ordered append/observer graph.
  The parameters a, b and recombination u are in distinct binder slots.
* [Outer access](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedUnionOuterAccessProof.lean):
  an original strict odd edge is required to read a lower outer state.
  Its J projection and the current left typed carrier derive current left
  J by original introduction, not by assuming current J in progress.
  The result projection yields the held outer lower-case interface.
  On an arbitrary open right term, #1527 inner induction uses #1528 actual
  progress under the same retained left-carrier and lower-left hypotheses.
* [Outer induction](../../LogicLineages/PersistentMarking/NumberedWindowInternalCertifiedUnionOuterInductionProof.lean):
  introduce the fresh b and its J premise inside the outer claim, then invoke
  the original #1517 odd progressive induction and instantiate the literal
  conclusion on the original a. The final conditional rule consumes genuine
  input J derivations and the same U report to derive J(u), in the original
  source body and arbitrary surrounding proof context.
* The exact source retains genuine `CountFit` on the actual scratch coding,
  `CertifiedOriginSplit` of #1519 (original strict certificates, at least
  one decrease, and same target recombination), and `UnionCarrierSupply`
  of #1528. The two internal arithmetic suppliers are **unproved premises**,
  and numeric fit is not used as semantic reflection. No installed count,
  occurrence transport/reconstructed witnesses, unconditional union, scalar
  induction, arithmetic accessibility or numbered promotion is claimed.

Native author status: source only; separate roots may audit the inner access
helper then the two exact outer declarations.
