# Internal oriented Bézout and binary CRT
Supplier 1: literal multiplication commutativity for arbitrary object terms and positive operator body, as a derivation in the original PA calculus. Supports conversion of signed coefficients to natural oriented coefficients; not a semantic Nat proof or a new axiom. Frozen before proof authoring; target compiler receipt follows.
3e8223c48382357f6f7efdd030ffd87ef5370d4da529f41e735130bae4d95ce4  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalMultiplicationCommutativityTargets.lean

Supplier 2: signed equation for A=succ(a), B=succ(b) gives literal certificate succ(u*A)=v*B with u=(z+x*b)+w*B, v=(x*A+y)+w*a. Consumer: actual object-language coprimality implies existence of the two oriented coefficients. This is a supporting internal arithmetic step toward paper06 internal level-two coding, not whole source completion. Targets frozen before proof authoring.
84b955cfb826789a209fe7af65f38918d6d8e143e3409d7f3f76dfee0ee933b7  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalOrientedBezoutDefinitions.lean
e71e5860c74a80bd008263a4c2aecd0cec054fc26c4e3eb0138a7f8172ac2f32  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalOrientedBezoutTargets.lean

Consumer 3: arbitrary positive object-language moduli succ(a), succ(b), arbitrary natural residue terms r,s, and arbitrary operator body. The original object-language coprimality implies existence of one shared natural c with literal congruent(c,r,succ(a)) and congruent(c,s,succ(b)). No oriented certificate is substituted for the coprimality premise. This closes binary internal CRT only; finite-family assembly and the full internal-level-two chain remain separate obligations. Frozen before consumer proof authoring.
82c8c2546172aa1704d04ba40f62824d26b05544ebe13b9773b77ba7109debd1  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalBinaryCRTDefinitions.lean
87151a3c3d12c6fe28206475d28305119e7b5db3b94aec371b34ab3238b6c4be  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/InternalBinaryCRTTargets.lean
