module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets
import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.RootExport

/-- Exact checked source undecidability interface. This is an alias proved
from the existing theorem, not an axiom or an extra target premise. -/
theorem undecidable :
    LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets.EncodedPolynomialUndecidable :=
  LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityProof.encodedPolynomialUndecidable

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.RootExport
#audit_namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemUndecidability.RootExport
