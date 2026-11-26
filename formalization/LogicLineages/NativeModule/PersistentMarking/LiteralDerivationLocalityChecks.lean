module

public import LogicLineages.NativeModule.PersistentMarking.LiteralDerivationCompleteProof
public import LogicLineages.NativeModule.PersistentMarking.LiteralDerivationSoundProof
public import LogicLineages.NativeModule.PersistentMarking.LiteralWindowLocalityProof

@[expose] public section

namespace LogicLineages.PersistentMarking.LiteralDerivationLocalityChecks
open LiteralDerivationLocalityTargets

theorem exact_CertificateExact : CertificateExact := by
  intro S J
  constructor
  · exact LiteralDerivationCompleteProof.complete S J
  · rintro ⟨tr⟩
    exact LiteralDerivationSoundProof.sound tr

theorem exact_SymbolicLocality : SymbolicLocality := LiteralWindowLocalityProof.locality

#print axioms exact_CertificateExact
#print axioms exact_SymbolicLocality

end LogicLineages.PersistentMarking.LiteralDerivationLocalityChecks
