# Complete semantic scalar compiler

The source recursion is the literal existing Scalar grammar. Only its coefficient evaluator changes: each shift calls the separately verified SemanticCoefficient.Code.recognize on the original closed coefficient syntax code. The BASE expansion is the identical accepted FiniteCoefficientBase.expand, preserving its equation and exact support. The numeric recursion uses the same original scalarSyntaxCode tags and pairing.

The value proof reproduces the prior scalar induction with the exact semantic recognizer theorem replacing the structural coefficient lemma. The literal-code proof reproduces the prior calibration induction with this evaluator. Compatibility is proved separately by induction and the recognizer's structuralExtension theorem; it states identical output syntax.

The actual numeric program is proved using the already checked finite decreasing graph children, actual recurrence equation, option combination, and primitive-recursive expansion. The graph conservatively evaluates both paired children in a shift, but the left result is ignored and the actual semantic coefficient recognizer is executed. Raw-code termination does not assume that recognition succeeds. No new premise, search, resource increase or baseline change is used.
