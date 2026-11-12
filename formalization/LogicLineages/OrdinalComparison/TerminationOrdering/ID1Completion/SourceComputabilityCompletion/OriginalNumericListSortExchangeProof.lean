module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixAdjacentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalNumericListSort OriginalNumericListSortExchange
open OriginalConstructorLeafInternalProof (sameKnownLeftRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] edge sourceEndpoint targetEndpoint front first second tail afterSecond afterFirst firstSecond secondFirst

theorem endpointsAt (source target certificate : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate))) :
 Nonempty (Derivation body Delta (graph3 sourceEndpoint source source target certificate)) ∧
 Nonempty (Derivation body Delta (graph3 targetEndpoint target source target certificate)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 have h := conjunctionRecover sourceMatch targetMatch xs (by simpa only [edge] using he)
 constructor
 · exact sameKnownLeftRecover (.projection 0) sourceEndpoint source xs
     (by simpa only [sourceMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using andLeft h)
     (projectionValue 0 xs)
 · exact sameKnownLeftRecover (.projection 1) targetEndpoint target xs
     (by simpa only [targetMatch,OriginalRawSyntaxTransport.sameOf,InternalApplicationStepPeel.same] using andRight h)
     (projectionValue 1 xs)

theorem acceptedAt (source target certificate left right : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)))
 (hl : Nonempty (Derivation body Delta (graph1 sort left source)))
 (hr : Nonempty (Derivation body Delta (graph1 sort right target))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 obtain ⟨hsource,htarget⟩ := endpointsAt source target certificate he
 let qs : Fin 8 → Program 3 := ![front,first,second,tail,afterSecond,afterFirst,firstSecond,secondFirst]
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j values Theta hj hq
 rw [equalRename]
 have hv : (fun i : Fin 3 => (xs i).relabel j) =
   Fin.cons (source.relabel j) (Fin.cons (target.relabel j) (Fin.cons (certificate.relabel j) Fin.elim0)) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 let ys : Fin 3 → OTerm beta := Fin.cons (source.relabel j)
   (Fin.cons (target.relabel j) (Fin.cons (certificate.relabel j) Fin.elim0))
 have hq' (i : Fin 8) : Nonempty (Derivation body Theta (programGraph (qs i) (values i) ys)) := by
   simpa only [hv,ys] using hq i
 have hs := renameInto hsource j Theta hj
 have ht := renameInto htarget j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [graph3Rename] at hs ht
 rw [graph1Rename] at hl' hr'
 have h0 : Nonempty (Derivation body Theta (programGraph front (values 0) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 0
 have h1 : Nonempty (Derivation body Theta (programGraph first (values 1) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 1
 have h2 : Nonempty (Derivation body Theta (programGraph second (values 2) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 2
 have h3 : Nonempty (Derivation body Theta (programGraph tail (values 3) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 3
 have h4 : Nonempty (Derivation body Theta (programGraph afterSecond (values 4) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 4
 have h5 : Nonempty (Derivation body Theta (programGraph afterFirst (values 5) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 5
 have h6 : Nonempty (Derivation body Theta (programGraph firstSecond (values 6) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 6
 have h7 : Nonempty (Derivation body Theta (programGraph secondFirst (values 7) ys)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.cons_val_succ] using hq' 7
 have hy := binaryRecover InternalListCodec.consCode second tail (values 4) (values 2) (values 3) ys
   (by simpa only [afterSecond,consOf] using h4) h2 h3
 have hx := binaryRecover InternalListCodec.consCode first tail (values 5) (values 1) (values 3) ys
   (by simpa only [afterFirst,consOf] using h5) h1 h3
 have hxy := binaryRecover InternalListCodec.consCode first afterSecond (values 6) (values 1) (values 4) ys
   (by simpa only [firstSecond,consOf] using h6) h1 h4
 have hyx := binaryRecover InternalListCodec.consCode second afterFirst (values 7) (values 2) (values 5) ys
   (by simpa only [secondFirst,consOf] using h7) h2 h5
 have hsAppend := binaryRecover InternalApplicationValidityStackAppend.append front firstSecond
   (source.relabel j) (values 0) (values 6) ys (by simpa only [sourceEndpoint] using hs) h0 h6
 have htAppend := binaryRecover InternalApplicationValidityStackAppend.append front secondFirst
   (target.relabel j) (values 0) (values 7) ys (by simpa only [targetEndpoint] using ht) h0 h7
 exact OriginalNumericListSortPrefixAdjacentProof.prefixAdjacentAt
   (values 0) (values 3) (values 1) (values 2) (values 4) (values 5) (values 6) (values 7)
   (source.relabel j) (target.relabel j) (left.relabel j) (right.relabel j)
   hy hxy hx hyx hsAppend htAppend hl' hr'

theorem acceptedEdgePreservesSort : OriginalNumericListSortExchangeTargets.AcceptedEdgePreservesSort := by
 intro body alpha source target certificate left right
 let H := graph3 edge (suc z) source target certificate ⊓
   (graph1 sort left source ⊓ graph1 sort right target)
 have h : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hv⟩ := acceptedAt source target certificate left right (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
 exact ⟨Derivation.implicationIntroduction hv⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeProof
