module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomTwoTickTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEmptyExpansionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro)
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof (arityTag3)
open OriginalContextInsertionLengthProof
open InternalApplicationValidityStackAppendListProof (appendZeroValue)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem childrenZero (raw typ parameter : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs z raw parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 have ht := unaryValue InternalUnpair.left (.projection 0) (numeral 3) raw xs (pairLeft raw (numeral 3) typ hr) (projectionValue 0 xs)
 have ha := arityTag3 (.projection 0) xs ht
 apply branchNumeralIntro 0 1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) _ _ z xs ha
 apply branchNumeralIntro 0 2 (OriginalRawSyntaxTransport.arityOf (.projection 0)) _ _ z xs ha
 exact constantValue 0 xs

theorem deletionZero (raw parameter c : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c z))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs z raw parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply programCases OriginalHereditaryExpansion.deletionJobs xs _
 intro beta rho Theta row hrho hrow
 let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hrow
 simp only [graph2Rename,zRelabel]
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename,zRelabel] at hp'
 have hl := OriginalHereditaryInternalExpansionLengthSupportProof.deletionLength
   (raw.relabel rho) (parameter.relabel rho) (c.relabel rho) z z row hp' lengthZero hrow
 exact outputTransport OriginalHereditaryExpansion.deletionJobs row z xx (lengthZeroRecover row hl) hrow

theorem rawZero (raw typ parameter c : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 3) typ)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c z))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion z raw parameter)) := by
 exact binaryValue InternalApplicationValidityStackAppend.append OriginalHereditaryExpansion.childJobs OriginalHereditaryExpansion.deletionJobs
   z z z (Fin.cons raw (Fin.cons parameter Fin.elim0)) (appendZeroValue z) (childrenZero raw typ parameter hr) (deletionZero raw parameter c hp)

theorem allZero (role typ raw : OTerm alpha) :
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll z role typ raw z)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons z Fin.elim0)))
 let ys : Fin 5 → OTerm alpha := Fin.cons z (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons z Fin.elim0))))
 apply compositionValue OriginalHereditaryAnnotatedExpansion.scan _ z xs ys
   (OriginalHereditaryInternalAnnotatedScanLengthProof.scanZero role typ raw z)
 intro i
 refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))))) i
 · exact unaryValue OriginalContextInsertion.length (.projection 3) z z xs lengthZero (projectionValue 3 xs)
 · exact projectionValue 0 xs
 · exact projectionValue 1 xs
 · exact projectionValue 2 xs
 · exact projectionValue 3 xs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEmptyExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomEmptyExpansionProof
