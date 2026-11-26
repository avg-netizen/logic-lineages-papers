module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open StructuralExchangeFields.AtFieldsProof (eqImp eqReverse)
open TransparentHeadBranches.Proof (andImp orImp identityImp applyImp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def active (U : Fin 19 → Program 3) (V : Program 3) := TransparentExchangeLayer.fields (fields U V)

theorem sideGraphs (U : Fin 19 → Program 3) (V : Program 3) (side : Bool)
    (node code param raw hd child enc res : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode side) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw hd child)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead enc hd)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult res hd))) :
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 7 else 0)) (numeral 4) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 9 else 2)) enc node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 18 else 17)) res node code param)) := by
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := ordinaryTag (TransparentChildFields.rawCode side) raw hd child xs hq hc
  have htag := successorBranchIntro V (InternalAcceptance.constantZero 3)
    (leftOf (TransparentChildFields.rawCode side)) (numeral 4) z xs hV ht
  have hh := (TransparentMetadataFields.InternalProof.ordinaryFields V side
    node code param raw hd child hV hq hc).2.1
  have henc := (EncodedMetadataFields.InternalProof.internalHeadFactor body alpha Delta V side
    node code param hd enc hh).mpr he
  have hres := (HeadResultFields.InternalProof.resultFactor body alpha Delta V side
    node code param hd res hh).mpr hr
  have hvec : xs = Fin.cons node (Fin.cons code (Fin.cons param Fin.elim0)) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hvec] at htag
  cases side with
  | false =>
    refine ⟨?_,?_,?_⟩
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields,
        TransparentTagFields.sourceTag,TransparentTagFields.sourceRawTag,
        TransparentChildFields.rawCode,leftOf,graph3,xs] using htag
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using henc
    · simpa [active,fields,TransparentExchangeLayer.fields] using hres
  | true =>
    refine ⟨?_,?_,?_⟩
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields,
        TransparentTagFields.targetTag,TransparentTagFields.targetRawTag,
        TransparentChildFields.rawCode,leftOf,graph3,xs] using htag
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using henc
    · simpa [active,fields,TransparentExchangeLayer.fields] using hres

theorem atFields : ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param source target f g base dest ef eg rf rg move h0 t0 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult rf f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult rg g)) →
  Nonempty (Derivation body Delta (graph3 (U 16) move node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  ∀ (ys : Fin 19 → OTerm alpha),
  (∀ i, Nonempty (Derivation body Delta (graph3 (active U V i) (ys i) node code param))) →
  (Nonempty (Derivation body Delta (graph3 (layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta
     ((eqn move (numeral 1) ⊓ eqn rg rf) ⊔ (eqn ef eg ⊓ eqn h0 (numeral 1))))) := by
  intro body alpha Delta U V node code param source target f g base dest ef eg rf rg move h0 t0
    hV hn hsource htarget hef heg hrf hrg hm hc ys hy
  obtain ⟨hqs,hqt⟩ := StructuralExchangeFields.SupportProof.rawSides node code param source target hn
  obtain ⟨hs0,hs2,hs17⟩ := sideGraphs U V false node code param source f base ef rf hV hqs hsource hef hrf
  obtain ⟨ht7,ht9,ht18⟩ := sideGraphs U V true node code param target g dest eg rg hV hqt htarget heg hrg
  have hm16 : Nonempty (Derivation body Delta (graph3 (active U V 16) move node code param)) := by
    simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hm
  have he0 := valueUnique (active U V 0) (ys 0) (numeral 4) ![node,code,param] (hy 0) hs0
  have he7 := valueUnique (active U V 7) (ys 7) (numeral 4) ![node,code,param] (hy 7) ht7
  have he2 := valueUnique (active U V 2) (ys 2) ef ![node,code,param] (hy 2) hs2
  have he9 := valueUnique (active U V 9) (ys 9) eg ![node,code,param] (hy 9) ht9
  have he17 := valueUnique (active U V 17) (ys 17) rf ![node,code,param] (hy 17) hs17
  have he18 := valueUnique (active U V 18) (ys 18) rg ![node,code,param] (hy 18) ht18
  have he16 := valueUnique (active U V 16) (ys 16) move ![node,code,param] (hy 16) hm16
  have hone : Nonempty (Derivation body Delta (eqn (numeral 1) (numeral 1))) :=
    ⟨InternalTagArithmeticSupportProof.refl _⟩
  have hf := TransparentHeadBranches.Proof.internalOrdinary body alpha Delta (fields U V) V
    node code param h0 t0 ys hV hy he0 he7 hc
  constructor
  · intro h
    exact applyImp (orImp (andImp (eqImp _ _ _ _ he16 hone) (eqImp _ _ _ _ he18 he17))
      (andImp (eqImp _ _ _ _ he2 he9) (identityImp _))) (hf.mp h)
  · intro h
    exact hf.mpr (applyImp (orImp
      (andImp (eqImp _ _ _ _ (eqReverse he16) hone)
        (eqImp _ _ _ _ (eqReverse he18) (eqReverse he17)))
      (andImp (eqImp _ _ _ _ (eqReverse he2) (eqReverse he9)) (identityImp _))) h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.SupportProof
