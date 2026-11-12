module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open OriginalInternalJobChildPacket OriginalInternalJobChildCasesTargets
open OriginalRawSyntaxTransportInternalParserSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lambdaFirstCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain child : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 let prev : Program 5 := OriginalTypedDecoder.predecessorOf (.projection 1)
 let hd : Program 5 := OriginalTypedDecoder.headOf (.projection 1)
 let tl : Program 5 := OriginalTypedDecoder.tailOf (.projection 1)
 let ext : Program 5 := .composition InternalListCodec.consCode ![.projection 2,.projection 3]
 let cp : Program 5 := pairOf (.projection 4) ext
 let an : Program 5 := pairOf (constant 5 0) tl
 let qs : Fin 7 → Program 5 := ![rightOf (.projection 0),prev,hd,tl,ext,cp,an]
 let xs : Fin 5 → OTerm alpha := ![raw,typ,domain,gamma,c]
 apply programsCases qs xs psi
 intro beta j Theta ys hinc hq
 let xx : Fin 5 → OTerm beta := ![raw.relabel j,typ.relabel j,domain.relabel j,gamma.relabel j,c.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
 rw [hx] at hq
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph2Rename] at hc' hp' hj'
 simp only [admissibleRename] at ha'
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.lambdaTag (.projection 0) (raw.relabel j) (domain.relabel j) (child.relabel j) xx (projectionValue 0 xx) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 1) (ys 0)
  (unaryRecover InternalUnpair.left (.projection 0) (numeral 1) (raw.relabel j) xx htag (projectionValue 0 xx))
  (unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx (hq 0) (projectionValue 0 xx))
 have ht := OriginalTypedDecoderInternalScalarProof.arrowFields (.projection 1) (typ.relabel j) (ys 2) (ys 3) xx (projectionValue 1 xx) (hq 2) (hq 3)
 have hpred := unaryRecover InternalEqualityTest.predecessor (.projection 1) (ys 1) (typ.relabel j) xx (hq 1) (projectionValue 1 xx)
 have hright := unaryRecover InternalUnpair.right prev (ys 3) (ys 1) xx (hq 3) (hq 1)
 have htail : Nonempty (Derivation body Theta (graph1 InternalListCodec.tailCode (ys 3) (typ.relabel j))) :=
  unaryValue InternalUnpair.right InternalEqualityTest.predecessor (ys 3) (ys 1) (Fin.cons (typ.relabel j) Fin.elim0) hright hpred
 have he := binaryRecover InternalListCodec.consCode (.projection 2) (.projection 3) (ys 4) (domain.relabel j) (gamma.relabel j) xx (hq 4) (projectionValue 2 xx) (projectionValue 3 xx)
 have hcp := binaryRecover InternalPairing.pairing (.projection 4) ext (ys 5) (c.relabel j) (ys 4) xx (hq 5) (projectionValue 4 xx) (hq 4)
 have hann := binaryRecover InternalPairing.pairing (constant 5 0) tl (ys 6) (numeral 0) (ys 3) xx (hq 6) (constantValue 0 xx) (hq 3)
 have packet := OriginalInternalJobChildLambdaFieldsProof.lambdaFirst H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (ys 0) (domain.relabel j) (child.relabel j) (ys 2) (ys 3) (ys 4) (ys 5)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) (ys 6) hc' hraw ht htail he hcp hp' hj' hann ha'
 exact next beta j Theta (numeral 0) (ys 3) (child.relabel j) (ys 4) (ys 5) (ys 6) hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildLambdaCasesProof
