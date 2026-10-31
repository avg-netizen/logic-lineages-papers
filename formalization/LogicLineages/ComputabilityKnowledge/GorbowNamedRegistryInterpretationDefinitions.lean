module

public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsDefinitions

@[expose] public section
/-! Explicit named-header overlay on a padded internal PR registry. Named
source symbols and actual internal calls are calibrated separately. This
neither extends the old total ground diagram nor identifies old/new full-L
interpretations, truth/revision grounds, or an adequate source Base. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowSourceRegistryPadding

def functionProgram (pF pR : Program 1) (code : Nat) : Nat :=
  match GorbowRegistryDecoder.decodeHeader code with
  | none => 0
  | some (arity,tag,args) =>
      if (arity,tag) ∈ functionNames ∧ args.length = arity then
        (dispatch (root pF pR) functionTag [code]).getD 0
      else GorbowPRDefiningEquations.functionProgram (root pF pR) code

def relationProgram (pF pR : Program 1) (code : Nat) : Bool :=
  match GorbowRegistryDecoder.decodeHeader code with
  | none => false
  | some (arity,tag,args) =>
      if (arity,tag) ∈ relationNames ∧ args.length = arity then
        decide (dispatch (root pF pR) (relationTag pF) [code] = some 1)
      else false

def interpretation (pF pR : Program 1) (I : Interpretation) : Interpretation :=
  { I with
      universalFunction := functionProgram pF pR
      universalRelation := fun code => relationProgram pF pR code = true }

end LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretation
