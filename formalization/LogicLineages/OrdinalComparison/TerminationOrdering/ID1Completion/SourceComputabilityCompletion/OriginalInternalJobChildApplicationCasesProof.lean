module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationCasesProof
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
theorem applicationFirstCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain fn arg : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 0) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 let ar : Program 3 := .composition InternalListCodec.consCode ![.projection 1,.projection 2]
 let an : Program 3 := pairOf (constant 3 0) ar
 let qs : Fin 4 → Program 3 := ![rightOf (.projection 0),rightOf (rightOf (.projection 0)),ar,an]
 let xs : Fin 3 → OTerm alpha := ![raw,domain,typ]
 apply programsCases qs xs psi
 intro beta j Theta ys hinc hq
 let xx : Fin 3 → OTerm beta := ![raw.relabel j,domain.relabel j,typ.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph3Rename] at hc'
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationTag (.projection 0) (raw.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) xx (projectionValue 0 xx) hc'
 have hdomain := OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationDomain (.projection 0) (raw.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) xx (projectionValue 0 xx) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 2) (ys 0)
  (unaryRecover InternalUnpair.left (.projection 0) (numeral 2) (raw.relabel j) xx htag (projectionValue 0 xx))
  (unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx (hq 0) (projectionValue 0 xx))
 have hdom := selectorPair (rightOf (.projection 0)) (ys 0) (domain.relabel j) (ys 1) xx (hq 0) hdomain (hq 1)
 have har := binaryRecover InternalListCodec.consCode (.projection 1) (.projection 2) (ys 2) (domain.relabel j) (typ.relabel j) xx (hq 2) (projectionValue 1 xx) (projectionValue 2 xx)
 have hann := binaryRecover InternalPairing.pairing (constant 3 0) ar (ys 3) (numeral 0) (ys 2) xx (hq 3) (constantValue 0 xx) (hq 2)
 have packet := OriginalInternalJobChildApplicationFieldsProof.applicationFirst H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (ys 0) (ys 1) (domain.relabel j) (fn.relabel j) (arg.relabel j) (ys 2)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) (ys 3) hc' hraw hdom har hp' hj' hann ha'
 exact next beta j Theta (numeral 0) (ys 2) (fn.relabel j) (gamma.relabel j) (parameter.relabel j) (ys 3) hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
theorem applicationSecondCases (H : Program 1) (M W : Program 2)
 (role typ raw cell parameter c gamma domain fn arg : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain fn arg)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.secondJob cell raw parameter)))
 (next : Consumer body Delta H M W (numeral 1) role typ raw cell parameter c gamma psi) :
 Nonempty (Derivation body Delta psi) := by
 let ar : Program 3 := .composition InternalListCodec.consCode ![.projection 1,.projection 2]
 let an : Program 3 := pairOf (constant 3 0) (.projection 1)
 let qs : Fin 4 → Program 3 := ![rightOf (.projection 0),rightOf (rightOf (.projection 0)),ar,an]
 let xs : Fin 3 → OTerm alpha := ![raw,domain,typ]
 apply programsCases qs xs psi
 intro beta j Theta ys hinc hq
 let xx : Fin 3 → OTerm beta := ![raw.relabel j,domain.relabel j,typ.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 have hc' := renameInto hc j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hj' := renameInto hj j Theta hinc
 simp only [graph3Rename] at hc'
 simp only [admissibleRename] at ha'
 simp only [graph2Rename] at hp' hj'
 have htag := OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationTag (.projection 0) (raw.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) xx (projectionValue 0 xx) hc'
 have hdomain := OriginalRawSyntaxTransportInternalConstructorFieldsProof.applicationDomain (.projection 0) (raw.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) xx (projectionValue 0 xx) hc'
 have hraw := reconstructPair (raw.relabel j) (numeral 2) (ys 0)
  (unaryRecover InternalUnpair.left (.projection 0) (numeral 2) (raw.relabel j) xx htag (projectionValue 0 xx))
  (unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx (hq 0) (projectionValue 0 xx))
 have hdom := selectorPair (rightOf (.projection 0)) (ys 0) (domain.relabel j) (ys 1) xx (hq 0) hdomain (hq 1)
 have har := binaryRecover InternalListCodec.consCode (.projection 1) (.projection 2) (ys 2) (domain.relabel j) (typ.relabel j) xx (hq 2) (projectionValue 1 xx) (projectionValue 2 xx)
 have hann := binaryRecover InternalPairing.pairing (constant 3 0) (.projection 1) (ys 3) (numeral 0) (domain.relabel j) xx (hq 3) (constantValue 0 xx) (projectionValue 1 xx)
 have packet := OriginalInternalJobChildApplicationFieldsProof.applicationSecond H M W
  (role.relabel j) (typ.relabel j) (raw.relabel j) (ys 0) (ys 1) (domain.relabel j) (fn.relabel j) (arg.relabel j) (ys 2)
  (parameter.relabel j) (c.relabel j) (gamma.relabel j) (cell.relabel j) (ys 3) hc' hraw hdom har hp' hj' hann ha'
 exact next beta j Theta (numeral 0) (domain.relabel j) (arg.relabel j) (gamma.relabel j) (parameter.relabel j) (ys 3) hinc
  (by simpa only [GuardedSourceSyntaxProof.numeralRename] using packet)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildApplicationCasesProof
