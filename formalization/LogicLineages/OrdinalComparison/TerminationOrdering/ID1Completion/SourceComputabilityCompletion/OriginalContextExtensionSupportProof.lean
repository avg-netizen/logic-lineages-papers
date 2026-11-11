module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof OriginalContextExtension
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs are the unchanged outer context, domain code, source Object and
independent body payload. These auxiliary programs never replace a source
checker or a component of the calibrated source/computability tuple. -/
def sourceContext : Program 4 := leftOf (.projection 2)
def sourceRaw : Program 4 := rightOf (.projection 2)
def outerParameter : Program 4 := pairOf (.projection 0) sourceContext
def extendedContext : Program 4 := consOf (.projection 1) sourceContext
def extendedParameter : Program 4 := pairOf (.projection 0) extendedContext
def extendedObject : Program 4 := pairOf extendedContext (.projection 3)

def runtimeQueries : Fin 6 → Program 4 :=
  ![sourceContext,sourceRaw,outerParameter,extendedContext,extendedParameter,extendedObject]

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- All companion graphs refer to the SAME six outputs. Original composition
elimination recovers each shared input, and reverse unpair reconstructs the
supplied source Object with its original context and raw payload. -/
theorem recoveredFromQueries (xs : Fin 4 → OTerm alpha) (ys : Fin 6 → OTerm alpha)
    (hs : ∀ i, Nonempty (Derivation body Gamma
      (programGraph (runtimeQueries i) (ys i) xs))) :
    Nonempty (Derivation body Gamma
      (Recovered (xs 0) (xs 1) (xs 2) (xs 3)
        (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))) := by
  have hl := unaryRecover InternalUnpair.left (.projection 2) (ys 0) (xs 2) xs
    (hs 0) (projectionValue 2 xs)
  have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 1) (xs 2) xs
    (hs 1) (projectionValue 2 xs)
  obtain ⟨ho⟩ := reconstructPair (xs 2) (ys 0) (ys 1) hl hr
  obtain ⟨hc⟩ := binaryRecover InternalListCodec.consCode (.projection 1) sourceContext
    (ys 3) (xs 1) (ys 0) xs (hs 3) (projectionValue 1 xs) (hs 0)
  obtain ⟨hp⟩ := binaryRecover InternalPairing.pairing (.projection 0) sourceContext
    (ys 2) (xs 0) (ys 0) xs (hs 2) (projectionValue 0 xs) (hs 0)
  obtain ⟨hbp⟩ := binaryRecover InternalPairing.pairing (.projection 0) extendedContext
    (ys 4) (xs 0) (ys 3) xs (hs 4) (projectionValue 0 xs) (hs 3)
  obtain ⟨hbo⟩ := binaryRecover InternalPairing.pairing extendedContext (.projection 3)
    (ys 5) (ys 3) (xs 3) xs (hs 5) (hs 3) (projectionValue 3 xs)
  exact ⟨Derivation.conjunctionIntroduction ho
    (Derivation.conjunctionIntroduction hc
      (Derivation.conjunctionIntroduction hp
        (Derivation.conjunctionIntroduction hbp hbo)))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionSupportProof
