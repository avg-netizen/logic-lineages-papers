module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open InternalApplicationStepPeelWitnessProof
theorem fieldsFromQueries
    (d e arrow s t a certificate k lifted : OTerm α) (ys : Fin 15 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (taggedEdge d e arrow s t a certificate k)))
    (hlift : Nonempty (Derivation body Gamma (graph4 edgeLift lifted d e a certificate)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (witnessQueries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a (Fin.cons k Fin.elim0))))))))) :
    Nonempty (Derivation body Gamma (graph1 InternalApplicationStepPeel.structuralGuard (suc z) lifted ⊓
 (graph1 InternalApplicationStepPeel.functionCode s lifted ⊓
 (graph1 InternalApplicationStepPeel.targetFunctionCode t lifted ⊓
 graph1 InternalApplicationStepPeel.peeledStep k lifted)))) := by
  let xs : Fin 6 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a (Fin.cons k Fin.elim0)))))
  apply OriginalTransparentApplicationFunctionPeelFieldsCoreProof.fieldsAtPairs d e arrow s t a certificate k lifted
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9)
    (ys 10) (ys 11) (ys 12) (ys 13) (ys 14) htag hlift
  · exact unaryRecover InternalUnpair.right (.projection 2) (ys 0) s xs (hq 0) (projectionValue 2 xs)
  · exact unaryRecover InternalUnpair.right (.projection 3) (ys 1) t xs (hq 1) (projectionValue 3 xs)
  · exact unaryRecover InternalUnpair.right (.projection 4) (ys 2) a xs (hq 2) (projectionValue 4 xs)
  · exact unaryRecover InternalUnpair.left (.projection 5) (ys 3) k xs (hq 3) (projectionValue 5 xs)
  · exact unaryRecover InternalUnpair.right (.projection 5) (ys 4) k xs (hq 4) (projectionValue 5 xs)
  · exact binaryRecover InternalPairing.pairing fpQuery apQuery (ys 5) (ys 0) (ys 2) xs
      (hq 5) (hq 0) (hq 2)
  · exact binaryRecover InternalPairing.pairing (.projection 0) scQuery (ys 6) d (ys 5) xs
      (hq 6) (projectionValue 0 xs) (hq 5)
  · exact binaryRecover InternalPairing.pairing (two 6) sbQuery (ys 7) positionTerm (ys 6) xs
      (hq 7) (twoValue xs) (hq 6)
  · exact binaryRecover InternalPairing.pairing tpQuery apQuery (ys 8) (ys 1) (ys 2) xs
      (hq 8) (hq 1) (hq 2)
  · exact binaryRecover InternalPairing.pairing (.projection 0) tcQuery (ys 9) d (ys 8) xs
      (hq 9) (projectionValue 0 xs) (hq 8)
  · exact binaryRecover InternalPairing.pairing (two 6) tbQuery (ys 10) positionTerm (ys 9) xs
      (hq 10) (twoValue xs) (hq 9)
  · exact binaryRecover InternalListCodec.consCode (two 6) pathQuery (ys 11) positionTerm (ys 3) xs
      (hq 11) (twoValue xs) (hq 3)
  · exact binaryRecover InternalPairing.pairing (.projection 1) snQuery (ys 12) e (ys 7) xs
      (hq 12) (projectionValue 1 xs) (hq 7)
  · exact binaryRecover InternalPairing.pairing (.projection 1) tnQuery (ys 13) e (ys 10) xs
      (hq 13) (projectionValue 1 xs) (hq 10)
  · exact binaryRecover InternalPairing.pairing prefixQuery payloadQuery (ys 14) (ys 11) (ys 4) xs
      (hq 14) (hq 11) (hq 4)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsQueryProof
