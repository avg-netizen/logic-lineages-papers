module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuard
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [domain,codomain,source,target,argument,parameter]. Each binary
leaf receives its actual selected coordinate and the unchanged parameter. -/
def atParameter (P : Program 2) (i : Fin 6) : Program 6 :=
  .composition P ![.projection i,.projection 5]

def typeGuard : Program 6 :=
  .composition InternalApplicationStepPeel.endpointTypeGuard
    ![.projection 0,.projection 1,.projection 2,.projection 3,.projection 4]

/-- The original seven tests remain literal: source-universe validity,
packed target validity, argument-universe validity, three raw type tags and
codomain membership. In particular, target validity has no universe filter. -/
def endpoint (sourceValid targetValid member : Program 2) : Program 6 :=
  InternalAcceptance.conjunction (atParameter sourceValid 2)
    (InternalAcceptance.conjunction (atParameter targetValid 3)
      (InternalAcceptance.conjunction (atParameter sourceValid 4)
        (InternalAcceptance.conjunction typeGuard (atParameter member 1))))

def selectedEndpoint (data : Data) : Program 6 :=
  endpoint (validity data) (targetValidity data) data.member

def graph6 {α : Type} (P : Program 6)
    (out d e s t a parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph P out ![d,e,s,t,a,parameter]

def accepted {α : Type} (sourceValid targetValid member : Program 2)
    (d e s t a parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph6 (endpoint sourceValid targetValid member)
    InternalOriginalStepGuard.one d e s t a parameter

def requirements {α : Type} (sourceValid targetValid member : Program 2)
    (arrow d e s t a parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 sourceValid InternalOriginalStepGuard.one s parameter ⊓
    (graph2 targetValid InternalOriginalStepGuard.one t parameter ⊓
      (graph2 sourceValid InternalOriginalStepGuard.one a parameter ⊓
        (InternalStructuralEndpointGuard.tagGraphs arrow d s t a ⊓
          graph2 member InternalOriginalStepGuard.one e parameter)))

def applicationPremises {α : Type} (data : Data)
    (arrow d e s t a sourceApp targetApp parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (accepted (validity data) (targetValidity data) data.member d e s t a parameter ⊓
      (graph4 application sourceApp d e s a ⊓ graph4 application targetApp d e t a))

/-- Both parent validity graphs and their literal raw result tags are
conclusions. The target retains only packed validity, exactly as in the
original endpoint. No semantic decoding or successful execution is assumed. -/
def applicationValidity {α : Type} (data : Data)
    (sourceApp targetApp codomain parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (validity data) InternalOriginalStepGuard.one sourceApp parameter ⊓
    (graph2 (targetValidity data) InternalOriginalStepGuard.one targetApp parameter ⊓
      (graph1 InternalUnpair.left codomain sourceApp ⊓
        graph1 InternalUnpair.left codomain targetApp))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuard
