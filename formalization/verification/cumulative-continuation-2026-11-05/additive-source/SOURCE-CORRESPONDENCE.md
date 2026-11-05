# Additive source fragment: source correspondence

This component connects the restricted linear-row endpoint back to the
original `CommonLayerSyntax.BaseTerm` and `SnyatkovCompletion.SourceFormula`
syntax. The source terms retain their original natural-number names and
usual numeral/addition semantics. The syntactic test excludes every Phi
node. Equality, strict order, negation, conjunction and existential
quantification remain unrestricted, including repeated names and arbitrary
quantifier nesting. Universal quantification and other Boolean connectives
are expressible using this original grammar.

The new supplier obligation is that every row introduced by a phi-free term's
existing postfix graph has only literal variable summands. From that property,
the complete prior source-row translation must pass the quantified-linearity
test. Admissibility is a proved output guarantee, not a new user premise or
an oracle attached to the generated formula.

The source compiler is the literal composition of the prior SourceRows
translation with QuantifiedLinear elimination. Its output has exactly the
original free-name membership. The closed-sentence endpoint accepts exactly
phi-free source formulas with no free names and gives the same truth value
under every environment. Rejection means outside this explicit fragment,
not falsehood. Numeric tests and compilers retain the existing radix-four
term and radix-five source encodings, with separate calibration and
primitive-recursiveness targets.

This proves only the additive first-order source fragment. It does not
eliminate arbitrary Phi occurrences or establish the general Snyatkov BASE
theorem. Nonlinear anchors, active-hyper assembly, dominant boundaries,
exhaustive source-case selection and global induction remain pending.
No numbered source-register statement is promoted by this component.
