module
public import LogicLineages.PermittedControl.SignedRowLowStripsTargets
import LogicLineages.PermittedControl.SignedRowLowStripsCodeProof
import LogicLineages.PermittedControl.SignedRowLowStripsSemanticProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_signedRowLowStripsCodeExact : SignedRowLowStrips.CodeExact :=
  SignedRowLowStrips.codeExact

theorem fixed_signedRowGuardedLowStrips : SignedRowLowStrips.GuardedLowRow :=
  SignedRowLowStrips.guardedLowRow

theorem fixed_fullSignedRowLowStrips : SignedRowLowStrips.FullSignedRowLowStrips :=
  ⟨fixed_signedRowLowStripsCodeExact,fixed_signedRowGuardedLowStrips⟩

#print axioms fixed_signedRowLowStripsCodeExact
#print axioms fixed_signedRowGuardedLowStrips
#print axioms fixed_fullSignedRowLowStrips

end LogicLineages.PermittedControl.StatementChecks
