import LogicLineages.PersistentMarking.LiteralDerivationCompleteProof
import LogicLineages.PersistentMarking.LiteralDerivationSoundProof
import LogicLineages.PersistentMarking.LiteralWindowLocalityProof

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
