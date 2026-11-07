module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Re-encode the decoded context using the ORIGINAL codecs. No raw unpair
projection or canonicality assumption on arbitrary input codes is used. -/
def gammaCode (o : Nat) : Nat :=
  ((Encodable.decode o : Option ContextUniform.Object).map
    (fun q => Encodable.encode q.1)).getD 0

def gammaValue (v : List.Vector Nat 1) : Nat := gammaCode (v.get 0)

/-- Original guard evaluated on the diagonal, including every raw input. -/
def objectValid (o : Nat) : Nat :=
  JointGammaDomain.guardValue (List.Vector.ofFn ![o,o])

/-- A concrete finite Program AST, using the same guard program twice. -/
def validity (p : Program 2) : Program 1 :=
  .composition p ![.projection 0,.projection 0]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibration
