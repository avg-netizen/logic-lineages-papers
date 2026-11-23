module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverBoundsProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverGrammarProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationPrimaryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverChecks
open NumberedWindowPrimaryCoverSyntax NumberedWindowPrimaryCoverTargets

theorem exact_PrimaryBounds : PrimaryBounds :=
  NumberedWindowPrimaryCoverBoundsProof.both

theorem exact_TermGrammarCoverage : TermGrammarCoverage :=
  NumberedWindowPrimaryCoverGrammarProof.term

theorem exact_ArgsGrammarCoverage : ArgsGrammarCoverage :=
  NumberedWindowPrimaryCoverGrammarProof.args

theorem exact_FinitePrimaryClassCover : FinitePrimaryClassCover := by
  intro S K C τ Q R hk hQ hPrim
  have hR := (NumberedWindowPreservationPrimaryProof.primary hk hPrim).mp hQ
  have e := NumberedWindowPrimaryCoverBoundsProof.term hPrim
  exact exact_TermGrammarCoverage S K C τ R (termBounds Q).numeral (termBounds Q).nodes
    hR (by simpa only [e] using Nat.le_refl (termBounds R).numeral)
      (by simpa only [e] using Nat.le_refl (termBounds R).nodes)

#print axioms exact_PrimaryBounds
#print axioms exact_TermGrammarCoverage
#print axioms exact_ArgsGrammarCoverage
#print axioms exact_FinitePrimaryClassCover

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverChecks
