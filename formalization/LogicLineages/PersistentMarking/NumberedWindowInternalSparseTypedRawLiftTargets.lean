module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)

/-- Exact four new guard calls at the wrapped endpoints. These are
genuine supplied graphs, not claims derived from the earlier child tape,
a numerical calibration, or a ValidWindow premise. -/
def liftedEndpointGuards {α : Type} (windowProg : Program 3) (syntaxProg : Program 1)
    (ctx cod src dst : OTerm α) : Formula α :=
  (programGraph syntaxProg (suc z) ![src] ⊓ programGraph syntaxProg (suc z) ![dst]) ⊓
  (programGraph windowProg (suc z) ![ctx,cod,src] ⊓
    programGraph windowProg (suc z) ![ctx,cod,dst])

/-- The original child function type is successor of the same polynomial
pair dom/cod; this is the repository's literal arrow code (not a tag node).
The raw term endpoints of the proposed parent use the same literal arg. -/
def liftInputs {α : Type} (root other windowProg : Program 3) (syntaxProg : Program 1)
    (ctx dom cod arg source child dest : OTerm α) : Formula α :=
  let src := auxiliaryTerm dom cod source arg
  let dst := auxiliaryTerm dom cod dest arg
  programGraph (typedRaw5 root other windowProg syntaxProg) (suc z)
    ![ctx,rawCons dom cod,source,child,dest] ⊓
  liftedEndpointGuards windowProg syntaxProg ctx cod src dst

/-- Genuine same-program typed lift on the exact original codomain tape.
The child and parent witness are the actual child and its tag5 wrapper. -/
def ExactOpenTypedRaw5FunctionLift : Prop :=
  ∀ (body : Positive (Fin 1)) (root other windowProg : Program 3) (syntaxProg : Program 1)
    (α : Type) (Γ : List (Formula α)) (ctx dom cod arg source child dest : OTerm α),
    let src := auxiliaryTerm dom cod source arg
    let wr := functionWitnessTerm child
    let dst := auxiliaryTerm dom cod dest arg
    let out := programGraph (typedRaw5 root other windowProg syntaxProg) (suc z) ![ctx,cod,src,wr,dst]
    Nonempty (Derivation body Γ
      ((liftInputs root other windowProg syntaxProg ctx dom cod arg source child dest).imp out))

/-- Keep both actual address reports and validators, and both successful
least calls on the same new raw endpoints, within the same fiber. Nothing
here transfers the least of the child terms or equates quotient args. -/
def liftedSingletonFacts {α : Type} (cv tv : Program 1) (least : Program 3)
    (left right ctx cod sourceClass destClass src dst : OTerm α) : Formula α :=
  addressReport left ctx cod sourceClass ⊓
    (addressReport right ctx cod destClass ⊓
      (unary cv (suc z) ctx ⊓
        (unary tv (suc z) cod ⊓
          (programGraph least (suc sourceClass) ![ctx,cod,src] ⊓
            programGraph least (suc destClass) ![ctx,cod,dst]))))

/-- The actual re-installable r accepts the supplied literal one-hop
certificate at the very same newly selected body. Least and endpoint
admission remain explicit hypotheses, not consequences of run lifting. -/
def ExactOpenInstalledTypedRaw5LiftedSingleton : Prop :=
  ∀ (i j cv tv : Program 1) (d root other windowProg least : Program 3) (syntaxProg : Program 1)
    (c : Nat) (α : Type) (Γ : List (Formula α))
    (left right ctx dom cod sourceClass destClass arg source child dest : OTerm α),
    let raw := typedRaw5 root other windowProg syntaxProg
    let R := addressPositive cv tv raw least
    let B := sourceBody (data i j R d) c
    let src := auxiliaryTerm dom cod source arg
    let wr := functionWitnessTerm child
    let dst := auxiliaryTerm dom cod dest arg
    let supplied := liftInputs root other windowProg syntaxProg ctx dom cod arg source child dest ⊓
      liftedSingletonFacts cv tv least left right ctx cod sourceClass destClass src dst
    Nonempty (Derivation B Γ (supplied.imp (accepts R left (singletonCertificate destClass src wr dst) right)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
