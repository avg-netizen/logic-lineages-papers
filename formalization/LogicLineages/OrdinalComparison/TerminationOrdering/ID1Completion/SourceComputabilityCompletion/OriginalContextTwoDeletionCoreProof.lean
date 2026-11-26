module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalClassContextAllPositionObserver (deleteAt)
open InternalListCodecSupportProof (consGraph)
open OriginalAllPositionContextDeleteBaseProof OriginalAllPositionContextDeleteConsProof
open OriginalAllPositionContextDeleteDropProof
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem secondInput (p : Program 2) (out first old new : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn old new)))
    (hg : Nonempty (Derivation body Delta (graph2 p out first old))) :
    Nonempty (Derivation body Delta (graph2 p out first new)) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta _ out
    (Fin.cons first (Fin.cons old Fin.elim0)) (Fin.cons first (Fin.cons new Fin.elim0)) _ hg
  intro t
  refine Fin.cases ?_ (fun k => ?_) t
  · change Nonempty (Derivation body Delta (equal first first))
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using
      (show Nonempty (Derivation body Delta (eqn first first)) from ⟨InternalTagArithmeticSupportProof.refl first⟩)
  · refine Fin.cases ?_ (fun e => Fin.elim0 e) k
    change Nonempty (Derivation body Delta (equal old new))
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using he

/-- Zero earlier cutoff, once actual original/upper cons coordinates and
one actual tail deletion have been queried. No source/native premise. -/
theorem zeroAtCons (gamma head tail upper upperTail lower left right j a b : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hu : Nonempty (Derivation body Delta (consGraph upper head upperTail)))
    (ht : Nonempty (Derivation body Delta (graph2 deleteAt upperTail j tail)))
    (hl : Nonempty (Derivation body Delta (graph2 deleteAt left z upper)))
    (hd : Nonempty (Derivation body Delta (graph2 deleteAt lower z gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 deleteAt right j lower)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup a z gamma)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup b (suc j) gamma))) :
    Nonempty (Derivation body Delta (equal left right ⊓
      (graph2 InternalRawListRecursion.lookup a z upper ⊓ graph2 InternalRawListRecursion.lookup b j lower))) := by
  have hdEq := valueUnique deleteAt lower tail (Fin.cons z (Fin.cons gamma Fin.elim0)) hd (deleteZero gamma head tail hc)
  have hrTail := secondInput deleteAt right j lower tail hdEq hr
  obtain ⟨hleft⟩ := valueUnique deleteAt left upperTail (Fin.cons z (Fin.cons upper Fin.elim0)) hl (deleteZero upper head upperTail hu)
  obtain ⟨hright⟩ := valueUnique deleteAt right upperTail (Fin.cons j (Fin.cons tail Fin.elim0)) hrTail ht
  have he : Nonempty (Derivation body Delta (equal left right)) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using
      (show Nonempty (Derivation body Delta (eqn left right)) from
        ⟨InternalTagArithmeticSupportProof.trans hleft (InternalTagArithmeticSupportProof.symm hright)⟩)
  have haEq := valueUnique InternalRawListRecursion.lookup head a (Fin.cons z (Fin.cons gamma Fin.elim0))
    (lookupZero gamma head tail hc) ha
  have haOut := outputTransport InternalRawListRecursion.lookup head a (Fin.cons z (Fin.cons upper Fin.elim0))
    haEq (lookupZero upper head upperTail hu)
  have hbTail := iffForward (lookupConsIff gamma head tail j b hc) hb
  obtain ⟨hdEq⟩ := hdEq
  have hbOut := secondInput InternalRawListRecursion.lookup b j tail lower
    ⟨InternalTagArithmeticSupportProof.symm hdEq⟩ hbTail
  exact andIntro he (andIntro haOut hbOut)

/-- Lift a smaller-cutoff result through actual common cons constructors.
This is the local successor induction step, not an assumed global square. -/
theorem successorResult (head upper upperTail lower lowerTail left leftTail right rightTail i j a b : OTerm alpha)
    (hu : Nonempty (Derivation body Delta (consGraph upper head upperTail)))
    (hd : Nonempty (Derivation body Delta (consGraph lower head lowerTail)))
    (hl : Nonempty (Derivation body Delta (consGraph left head leftTail)))
    (hr : Nonempty (Derivation body Delta (consGraph right head rightTail)))
    (hi : Nonempty (Derivation body Delta (equal leftTail rightTail ⊓
      (graph2 InternalRawListRecursion.lookup a i upperTail ⊓ graph2 InternalRawListRecursion.lookup b j lowerTail)))) :
    Nonempty (Derivation body Delta (equal left right ⊓
      (graph2 InternalRawListRecursion.lookup a (suc i) upper ⊓ graph2 InternalRawListRecursion.lookup b (suc j) lower))) := by
  have he : Nonempty (Derivation body Delta (eqn leftTail rightTail)) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using andLeft hi
  have hl' := secondInput InternalListCodec.consCode left head leftTail rightTail he hl
  have hp := valueUnique InternalListCodec.consCode left right (Fin.cons head (Fin.cons rightTail Fin.elim0)) hl' hr
  have hout : Nonempty (Derivation body Delta (equal left right)) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using hp
  exact andIntro hout (andIntro
    (iffBackward (lookupConsIff upper head upperTail i a hu) (andLeft (andRight hi)))
    (iffBackward (lookupConsIff lower head lowerTail j b hd) (andRight (andRight hi))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionCoreProof
