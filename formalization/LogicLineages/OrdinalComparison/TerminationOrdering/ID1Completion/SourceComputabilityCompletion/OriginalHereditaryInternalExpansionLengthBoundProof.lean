module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionMeasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc eqn sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryInternalWeightDefinitions
open OriginalHereditaryInternalExpansionLengthRowsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromLength (role typ input rawJobs output actual known contextCount nodes W : OTerm alpha)
 (hdec : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll output role typ input rawJobs)))
 (hlen : Nonempty (Derivation body Delta (lengthGraph actual output)))
 (hknown : Nonempty (Derivation body Delta (lengthGraph known rawJobs)))
 (hw : Nonempty (Derivation body Delta (eqn W (mass contextCount nodes))))
 (hb : Nonempty (Derivation body Delta (ltF known (suc (suc (suc (mass contextCount nodes))))))) :
 Nonempty (Derivation body Delta (ltF actual (suc (suc (suc W))))) := by
 have houtput := OriginalHereditaryInternalExpansionLengthSupportProof.annotationLength role typ input rawJobs output known hdec hknown
 have he := valueUnique length actual known (Fin.cons output Fin.elim0) hlen houtput
 obtain ⟨hw⟩ := hw
 exact strictTransport actual (suc (suc (suc W))) known (suc (suc (suc (mass contextCount nodes))))
   he ⟨congSuc (congSuc (congSuc hw))⟩ hb

theorem fromView (role typ input rawJobs output actual contextCount nodes W : OTerm alpha)
 (hdec : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll output role typ input rawJobs)))
 (hlen : Nonempty (Derivation body Delta (lengthGraph actual output)))
 (hview : Nonempty (Derivation body Delta (LengthView contextCount rawJobs)))
 (hw : Nonempty (Derivation body Delta (eqn W (mass contextCount nodes)))) :
 Nonempty (Derivation body Delta (ltF actual (suc (suc (suc W))))) := by
 apply orCases hview
 · intro Theta inc hl
   exact fromLength role typ input rawJobs output actual contextCount contextCount nodes W
     (weakenProof hdec inc) (weakenProof hlen inc) hl (weakenProof hw inc)
     (OriginalHereditaryInternalExpansionLengthArithmeticProof.zeroChildren contextCount nodes)
 · intro Theta inc hrest
   apply orCases hrest
   · intro Xi inc2 hl
     exact fromLength role typ input rawJobs output actual (suc contextCount) contextCount nodes W
       (weakenProof (weakenProof hdec inc) inc2) (weakenProof (weakenProof hlen inc) inc2) hl
       (weakenProof (weakenProof hw inc) inc2)
       (OriginalHereditaryInternalExpansionLengthArithmeticProof.oneChild contextCount nodes)
   · intro Xi inc2 hl
     exact fromLength role typ input rawJobs output actual (suc (suc contextCount)) contextCount nodes W
       (weakenProof (weakenProof hdec inc) inc2) (weakenProof (weakenProof hlen inc) inc2) hl
       (weakenProof (weakenProof hw inc) inc2)
       (OriginalHereditaryInternalExpansionLengthArithmeticProof.twoChildren contextCount nodes)

theorem atCoordinates (parent parentRaw input parameter window gamma role typ rawJobs output actual W : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget parentRaw parent)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parentRaw input parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hraw : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs input parameter)))
 (hdec : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll output role typ input rawJobs)))
 (hlen : Nonempty (Derivation body Delta (lengthGraph actual output)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent))) :
 Nonempty (Derivation body Delta (ltF actual (suc (suc (suc W))))) := by
 apply OriginalHereditaryInternalExpansionMeasureProof.measuresCases input input gamma _
 intro beta rho Theta nodes ignored count hrho hn hi hl
 simp only [orderRename,sucRelabel]
 have hp' := renameInto hp rho Theta hrho
 have hr' := renameInto hr rho Theta hrho
 have hparam' := renameInto hparam rho Theta hrho
 have hraw' := renameInto hraw rho Theta hrho
 have hdec' := renameInto hdec rho Theta hrho
 have hlen' := renameInto hlen rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 simp only [graph1Rename,graph2Rename,graph4Rename,lengthRename] at hp' hr' hparam' hraw' hdec' hlen' hw'
 have hfields := OriginalHereditaryInternalExpansionFieldsProof.fieldsOfForget
   (parent.relabel rho) (parentRaw.relabel rho) (input.relabel rho) (parameter.relabel rho)
   (window.relabel rho) (gamma.relabel rho) hp' hr' hparam'
 have hweight := OriginalHereditaryInternalWeightValueProof.weightEqual
   (parent.relabel rho) (input.relabel rho) (gamma.relabel rho) count nodes (W.relabel rho) hfields hl hn hw'
 have hview := OriginalHereditaryInternalExpansionLengthRawProof.rawLengthView
   (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
   count (rawJobs.relabel rho) hparam' hl hraw'
 exact fromView (role.relabel rho) (typ.relabel rho) (input.relabel rho) (rawJobs.relabel rho)
   (output.relabel rho) (actual.relabel rho) count nodes (W.relabel rho) hdec' hlen' hview hweight

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthBoundProof
