module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel eqn)
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalFiniteBlocksSubstitutionProof (renameIdentity)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryInternalFinitePrefixCasesTargets
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryCases : Unary := by
 intro body alpha Delta front first suffix joined count index value psi hc ha hl hb hv firstCase tailCase
 have hcons := OriginalHereditaryInternalFinitePrefixAppendProof.unaryAppended front first suffix joined hc ha
 apply OriginalHereditaryInternalFinitePrefixProof.boundedCons body alpha Delta joined first suffix count index value psi hcons hl hb hv
 · intro Theta inc he
   have hh := firstCase alpha id Theta (by intro f hf; simpa only [renameIdentity] using inc f hf)
     (by simpa only [Term.relabel_id] using he)
   simpa only [renameIdentity] using hh
 · exact tailCase

theorem binaryCases : Binary := by
 intro body alpha Delta front first middle second suffix joined count index value psi hc ht ha hl hb hv firstCase secondCase tailCase
 apply programCases InternalListCodec.consCode (Fin.cons second (Fin.cons suffix Fin.elim0)) _
 intro beta j Theta result hj hr
 simp only [consTermRename,emptyRename] at hr
 have hc' := renameInto hc j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [consGraphRename,zRelabel] at hc' ht'
 have ha' := renameInto ha j Theta hj
 rw [graph2Rename] at ha'
 have hl' := renameInto hl j Theta hj
 rw [lengthRename] at hl'
 have hb' := renameInto hb j Theta hj
 simp only [Below,InternalOriginalOrderSyntaxProof.orderRename] at hb'
 have hv' := renameInto hv j Theta hj
 rw [graph2Rename] at hv'
 have hcons := OriginalHereditaryInternalFinitePrefixAppendProof.binaryAppended
   (front.relabel j) (first.relabel j) (middle.relabel j) (second.relabel j)
   (suffix.relabel j) result (joined.relabel j) hc' ht' hr ha'
 apply OriginalHereditaryInternalFinitePrefixProof.boundedCons body beta Theta
   (joined.relabel j) (first.relabel j) result (count.relabel j) (index.relabel j) (value.relabel j)
   (psi.relabel j) hcons hl' hb' hv'
 · intro Xi inc he
   exact firstCase beta j Xi (fun f hf => inc _ (hj f hf)) he
 · intro gamma k Xi pred tailCount hk hlength hbound hlookup
   have hr' := renameInto hr k Xi hk
   rw [graph2Rename] at hr'
   apply OriginalHereditaryInternalFinitePrefixProof.boundedCons body gamma Xi
     (result.relabel k) ((second.relabel j).relabel k) ((suffix.relabel j).relabel k)
     tailCount pred ((value.relabel j).relabel k) ((psi.relabel j).relabel k) hr' hlength hbound hlookup
   · intro Omega inc he
     have incl : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Omega := by
       intro f hf
       simpa only [← formulaRelabelComposition] using inc _ (hk _ (hj f hf))
     have hh := secondCase gamma (k ∘ j) Omega incl (by simpa only [Term.relabel_relabel] using he)
     simpa only [formulaRelabelComposition] using hh
   · intro omega l Omega pred' tailCount' hlinc hlength' hbound' hlookup'
     have incl : ∀ f ∈ Delta, f.relabel (l ∘ k ∘ j) ∈ Omega := by
       intro f hf
       simpa only [← formulaRelabelComposition,Function.comp_assoc] using hlinc _ (hk _ (hj f hf))
     have hh := tailCase omega (l ∘ k ∘ j) Omega pred' tailCount' incl
       (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hlength') hbound'
       (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hlookup')
     simpa only [formulaRelabelComposition,Function.comp_assoc] using hh
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixCasesProof
