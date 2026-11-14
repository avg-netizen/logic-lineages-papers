module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open StructuralExchangeFields StructuralExchangeFields.SupportProof
open StructuralExchangeFields.AtFieldsProof (eqImp eqReverse)
open TransparentHeadBranches.Proof (andImp identityImp applyImp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sideGraphs (U : Fin 19 → Program 3) (V : Program 3) (side : Bool)
    (node code param raw domain child : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode side) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child))) :
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 7 else 0)) (numeral 1) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 8 else 1)) domain node code param)) := by
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := lambdaTag (TransparentChildFields.rawCode side) raw domain child xs hq hc
  have htag := successorBranchIntro V (InternalAcceptance.constantZero 3)
    (leftOf (TransparentChildFields.rawCode side)) (numeral 1) z xs hV ht
  obtain ⟨ha,_,_,_⟩ := TransparentMetadataFields.InternalProof.lambdaFields V side
    node code param raw domain child hV hq hc
  have hvec : xs = Fin.cons node (Fin.cons code (Fin.cons param Fin.elim0)) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hvec] at htag
  cases side with
  | false =>
    refine ⟨?_,?_⟩
    · simpa [active,fields,TransparentExchangeLayer.fields,TransparentTagFields.sourceTag,
        TransparentTagFields.sourceRawTag,TransparentChildFields.rawCode,leftOf,graph3,xs] using htag
    · simpa [active,fields,TransparentExchangeLayer.fields,EncodedMetadataFields.annotation] using ha
  | true =>
    refine ⟨?_,?_⟩
    · simpa [active,fields,TransparentExchangeLayer.fields,TransparentTagFields.targetTag,
        TransparentTagFields.targetRawTag,TransparentChildFields.rawCode,leftOf,graph3,xs] using htag
    · simpa [active,fields,TransparentExchangeLayer.fields,EncodedMetadataFields.annotation] using ha

theorem atFields (U : Fin 19 → Program 3) (V : Program 3) : ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node code param source target sigma tau q r h0 t0 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  ∀ (ys : Fin 19 → OTerm alpha),
  (∀ i, Nonempty (Derivation body Delta (graph3 (active U V i) (ys i) node code param))) →
  (Nonempty (Derivation body Delta (graph3 (StructuralExchangeFields.layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn sigma tau ⊓ eqn h0 (numeral 1)))) := by
  intro body alpha Delta node code param source target sigma tau q r h0 t0 hV hn hsource htarget hc ys hy
  obtain ⟨hqs,hqt⟩ := rawSides node code param source target hn
  obtain ⟨hs0,hs1⟩ := LambdaSupportProof.sideGraphs U V false node code param source sigma q hV hqs hsource
  obtain ⟨ht7,ht8⟩ := LambdaSupportProof.sideGraphs U V true node code param target tau r hV hqt htarget
  have he0 := valueUnique (active U V 0) (ys 0) (numeral 1) ![node,code,param] (hy 0) hs0
  have he7 := valueUnique (active U V 7) (ys 7) (numeral 1) ![node,code,param] (hy 7) ht7
  have he1 := valueUnique (active U V 1) (ys 1) sigma ![node,code,param] (hy 1) hs1
  have he8 := valueUnique (active U V 8) (ys 8) tau ![node,code,param] (hy 8) ht8
  have hf := TransparentExchangeLayer.InternalProof.internalLambda body alpha Delta (fields U V) V
    node code param h0 t0 ys hV hy he0 he7 hc
  constructor
  · intro h
    exact applyImp (andImp (eqImp _ _ _ _ he1 he8) (identityImp _)) (hf.mp h)
  · intro h
    exact hf.mpr (applyImp (andImp (eqImp _ _ _ _ (eqReverse he1) (eqReverse he8)) (identityImp _)) h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaSupportProof
