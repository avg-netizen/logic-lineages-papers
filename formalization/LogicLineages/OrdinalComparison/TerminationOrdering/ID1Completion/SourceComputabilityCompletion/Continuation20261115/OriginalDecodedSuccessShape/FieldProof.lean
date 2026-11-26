module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.LayerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.FieldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm trans)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114.TransparentHeadBranches.Proof (andImp orImp applyImp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def actualFields (n : Nat) (arity : Fin n → Nat) : Fin 19 → Program 3 :=
  TransparentExchangeLayer.fields (StructuralExchangeFields.fields
    (OriginalDecodedLambdaRecurrence.LayerProof.filled n arity (OriginalDecodedLayerCalibration.guard n))
    (OriginalDecodedLayerCalibration.guard n))
theorem sourceField (n : Nat) (arity : Fin n → Nat) :
    actualFields n arity 0 = TransparentTagFields.sourceTag (OriginalDecodedLayerCalibration.guard n) := by
  simp only [actualFields,TransparentExchangeLayer.fields,StructuralExchangeFields.fields,
    if_neg (by decide : (0 : Fin 19) ≠ 14),if_neg (by decide : (0 : Fin 19) ≠ 15),if_pos rfl,if_true]
theorem targetField (n : Nat) (arity : Fin n → Nat) :
    actualFields n arity 7 = TransparentTagFields.targetTag (OriginalDecodedLayerCalibration.guard n) := by
  simp only [actualFields,TransparentExchangeLayer.fields,StructuralExchangeFields.fields,
    if_neg (by decide : (7 : Fin 19) ≠ 14),if_neg (by decide : (7 : Fin 19) ≠ 15),
    if_neg (by decide : (7 : Fin 19) ≠ 0),
    if_neg (by decide : (7 : Fin 19) ≠ 1),
    if_neg (by decide : (7 : Fin 19) ≠ 2),
    if_neg (by decide : (7 : Fin 19) ≠ 3),
    if_neg (by decide : (7 : Fin 19) ≠ 4),
    if_neg (by decide : (7 : Fin 19) ≠ 5),
    if_neg (by decide : (7 : Fin 19) ≠ 6),
    if_pos rfl,if_true]

theorem atomTransport (s t : OTerm alpha) (k : Nat)
    (he : Nonempty (Derivation body Delta (eqn s t))) :
    Nonempty (Derivation body Delta ((eqn s (numeral k)).imp (eqn t (numeral k)))) := by
  let A := eqn s (numeral k)
  obtain ⟨he⟩ := withHyp he A
  have ha : Derivation body (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction (trans (symm he) ha)⟩
theorem activeTransport (s t : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn s t)))
    (ha : Nonempty (Derivation body Delta (Targets.active s))) :
    Nonempty (Derivation body Delta (Targets.active t)) := by
  exact applyImp (orImp (atomTransport s t 1 he) (orImp (atomTransport s t 2 he)
    (orImp (atomTransport s t 4 he) (orImp (atomTransport s t 5 he) (atomTransport s t 7 he))))) ha

theorem atFields (n : Nat) (arity : Fin n → Nat)
    (node source target st sp tt tp answers param : OTerm alpha) (xs : Fin 19 → OTerm alpha)
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source st sp)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tt tp)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node answers param)))
    (hl : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) (numeral 2) node answers param)))
    (hq : ∀ i, Nonempty (Derivation body Delta (graph3 (actualFields n arity i) (xs i) node answers param))) :
    Nonempty (Derivation body Delta (eqn st tt ⊓ Targets.active st)) := by
  let U := StructuralExchangeFields.fields
    (OriginalDecodedLambdaRecurrence.LayerProof.filled n arity (OriginalDecodedLayerCalibration.guard n))
    (OriginalDecodedLayerCalibration.guard n)
  have ho : Nonempty (Derivation body Delta
      (graph3 (TransparentExchangeLayer.optional U (OriginalDecodedLayerCalibration.guard n)) (numeral 2) node answers param)) := by
    simpa only [OriginalDecodedLayerCalibration.layer,OriginalDecodedLambdaRecurrence.LayerProof.layerIdentity,
      StructuralExchangeFields.layer,U] using hl
  have hb := (TransparentExchangeLayer.InternalProof.internalBodyFactor body alpha Delta U
    (OriginalDecodedLayerCalibration.guard n) node answers param (numeral 1) xs hg hq).mp ho
  have hshape := LayerProof.successShape xs hb
  have htags := TransparentTagFields.InternalProof.internalTags body alpha Delta
    (OriginalDecodedLayerCalibration.guard n) node answers param source target st sp tt tp hg hn hs ht
  have h0 := hq 0
  rw [sourceField] at h0
  have h7 := hq 7
  rw [targetField] at h7
  have he0 := valueUnique (TransparentTagFields.sourceTag (OriginalDecodedLayerCalibration.guard n)) (xs 0) st ![node,answers,param] h0 htags.1
  have he7 := valueUnique (TransparentTagFields.targetTag (OriginalDecodedLayerCalibration.guard n)) (xs 7) tt ![node,answers,param] h7 htags.2
  have ha := activeTransport (xs 0) st he0 (andRight hshape)
  obtain ⟨he0⟩ := he0
  obtain ⟨he7⟩ := he7
  obtain ⟨he⟩ := andLeft hshape
  exact andIntro ⟨trans (symm he0) (trans he he7)⟩ ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.FieldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.FieldProof
