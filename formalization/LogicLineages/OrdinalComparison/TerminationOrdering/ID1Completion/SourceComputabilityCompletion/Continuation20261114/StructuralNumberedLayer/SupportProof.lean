module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.AtFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.SupportProof
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

open ResultStructuralFields ResultStructuralFields.SupportProof (active)
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
theorem sideGraphs (U : Fin 19 → Program 3) (V : Program 3) (side : Bool)
    (node code param raw rank hd tau base ts extras enc : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode side) raw node code param)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw
      ![rank,hd,tau,base,ts,extras])))
    (he : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead enc hd))) :
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 7 else 0)) (numeral 5) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 8 else 1)) (tau) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 9 else 2)) (enc) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 10 else 3)) (rank) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 11 else 4)) (ts) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 12 else 5)) (base) node code param)) ∧
    Nonempty (Derivation body Delta (graph3 (active U V (if side then 13 else 6)) (extras) node code param)) := by
  let query := TransparentChildFields.rawCode side
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := numberedTag query raw rank hd tau base ts extras xs hq hc
  have htag := successorBranchIntro V (InternalAcceptance.constantZero 3)
    (leftOf query) (numeral 5) z xs hV ht
  obtain ⟨ha,hh,hl,hts⟩ := EncodedMetadataFields.InternalProof.internalNumbered body alpha Delta V side
    node code param raw rank hd enc tau base ts extras hV hq hc he
  obtain ⟨hb,hext⟩ := TransparentChildFields.InternalProof.binaryChildren V side node code param base extras hV
    (numberedArity query raw rank hd tau base ts extras xs hq hc)
    (numberedFirst query raw rank hd tau base ts extras xs hq hc)
    (numberedSecond query raw rank hd tau base ts extras xs hq hc)
  have hvec : xs = Fin.cons node (Fin.cons code (Fin.cons param Fin.elim0)) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hvec] at htag
  cases side with
  | false =>
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields,
        TransparentTagFields.sourceTag,TransparentTagFields.sourceRawTag,
        TransparentChildFields.rawCode,leftOf,graph3,xs,query] using htag
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using ha
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hh
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hl
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hts
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hb
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hext
  | true =>
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields,
        TransparentTagFields.targetTag,TransparentTagFields.targetRawTag,
        TransparentChildFields.rawCode,leftOf,graph3,xs,query] using htag
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using ha
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hh
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hl
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hts
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hb
    · simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hext

theorem atFields : ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param source target k l f g tau upsilon base dest ts us extras otherExtras
      ef eg move h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source
    ![k,f,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target
    ![l,g,upsilon,dest,us,otherExtras])) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  Nonempty (Derivation body Delta (graph3 (U 16) move node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  ∀ (ys : Fin 19 → OTerm alpha),
  (∀ i, Nonempty (Derivation body Delta (graph3 (active U V i) (ys i) node code param))) →
  (Nonempty (Derivation body Delta
      (graph3 (ResultStructuralFields.layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta ((eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)) ⊓
     (((eqn extras otherExtras ⊓ eqn move (numeral 1)) ⊔
       ((eqn ef eg ⊓ eqn extras otherExtras) ⊓ eqn h0 (numeral 1))) ⊔
      ((eqn ef eg ⊓ eqn base dest) ⊓ eqn h3 (numeral 1)))))) := by
  intro body alpha Delta U V node code param source target k l f g tau upsilon base dest ts us extras otherExtras
    ef eg move h0 t0 h1 t1 h2 t2 h3 t3 hV hn hsource htarget hef heg hm hc0 hc1 hc2 hc3 ys hy
  obtain ⟨hqs,hqt⟩ := StructuralExchangeFields.SupportProof.rawSides node code param source target hn
  obtain ⟨hs0,hs1,hs2,hs3,hs4,hs5,hs6⟩ := sideGraphs U V false
    node code param source k f tau base ts extras ef hV hqs hsource hef
  obtain ⟨ht7,ht8,ht9,ht10,ht11,ht12,ht13⟩ := sideGraphs U V true
    node code param target l g upsilon dest us otherExtras eg hV hqt htarget heg
  have hm16 : Nonempty (Derivation body Delta (graph3 (active U V 16) move node code param)) := by
    simpa [active,fields,StructuralExchangeFields.fields,TransparentExchangeLayer.fields] using hm
  have he0 := valueUnique (active U V 0) (ys 0) (numeral 5) ![node,code,param] (hy 0) hs0
  have he1 := valueUnique (active U V 1) (ys 1) tau ![node,code,param] (hy 1) hs1
  have he2 := valueUnique (active U V 2) (ys 2) ef ![node,code,param] (hy 2) hs2
  have he3 := valueUnique (active U V 3) (ys 3) k ![node,code,param] (hy 3) hs3
  have he4 := valueUnique (active U V 4) (ys 4) ts ![node,code,param] (hy 4) hs4
  have he5 := valueUnique (active U V 5) (ys 5) base ![node,code,param] (hy 5) hs5
  have he6 := valueUnique (active U V 6) (ys 6) extras ![node,code,param] (hy 6) hs6
  have he7 := valueUnique (active U V 7) (ys 7) (numeral 5) ![node,code,param] (hy 7) ht7
  have he8 := valueUnique (active U V 8) (ys 8) upsilon ![node,code,param] (hy 8) ht8
  have he9 := valueUnique (active U V 9) (ys 9) eg ![node,code,param] (hy 9) ht9
  have he10 := valueUnique (active U V 10) (ys 10) l ![node,code,param] (hy 10) ht10
  have he11 := valueUnique (active U V 11) (ys 11) us ![node,code,param] (hy 11) ht11
  have he12 := valueUnique (active U V 12) (ys 12) dest ![node,code,param] (hy 12) ht12
  have he13 := valueUnique (active U V 13) (ys 13) otherExtras ![node,code,param] (hy 13) ht13
  have he16 := valueUnique (active U V 16) (ys 16) move ![node,code,param] (hy 16) hm16
  have hone : Nonempty (Derivation body Delta (eqn (numeral 1) (numeral 1))) :=
    ⟨InternalTagArithmeticSupportProof.refl _⟩
  have hf := TransparentHeadBranches.Proof.internalNumbered body alpha Delta (fields U V) V
    node code param h0 t0 h1 t1 h2 t2 h3 t3 ys hV hy he0 he7 hc0 hc1 hc2 hc3
  constructor
  · intro h
    exact applyImp (andImp (andImp (eqImp _ _ _ _ he3 he10) (andImp (eqImp _ _ _ _ he1 he8) (eqImp _ _ _ _ he4 he11))) (orImp (orImp (andImp (eqImp _ _ _ _ he6 he13) (eqImp _ _ _ _ he16 hone)) (andImp (andImp (eqImp _ _ _ _ he2 he9) (eqImp _ _ _ _ he6 he13)) (identityImp _))) (andImp (andImp (eqImp _ _ _ _ he2 he9) (eqImp _ _ _ _ he5 he12)) (identityImp _)))) (hf.mp h)
  · intro h
    exact hf.mpr (applyImp (andImp (andImp (eqImp _ _ _ _ (eqReverse he3) (eqReverse he10)) (andImp (eqImp _ _ _ _ (eqReverse he1) (eqReverse he8)) (eqImp _ _ _ _ (eqReverse he4) (eqReverse he11)))) (orImp (orImp (andImp (eqImp _ _ _ _ (eqReverse he6) (eqReverse he13)) (eqImp _ _ _ _ (eqReverse he16) hone)) (andImp (andImp (eqImp _ _ _ _ (eqReverse he2) (eqReverse he9)) (eqImp _ _ _ _ (eqReverse he6) (eqReverse he13))) (identityImp _))) (andImp (andImp (eqImp _ _ _ _ (eqReverse he2) (eqReverse he9)) (eqImp _ _ _ _ (eqReverse he5) (eqReverse he12))) (identityImp _)))) h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.SupportProof
