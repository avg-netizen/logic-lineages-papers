module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralNumberedLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {b : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem factor (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (node code param f base g dest ss ts out : OTerm alpha)
    (hV : Nonempty (Derivation b Delta (graph3 V (numeral 1) node code param)))
    (hp : Nonempty (Derivation b Delta (graph2 InternalPairing.pairing param ss ts)))
    (hf : Nonempty (Derivation b Delta (graph3 (TransparentMetadataFields.head V false) f node code param)))
    (hb : Nonempty (Derivation b Delta (graph3 (TransparentChildFields.first V false) base node code param)))
    (hg : Nonempty (Derivation b Delta (graph3 (TransparentMetadataFields.head V true) g node code param)))
    (hd : Nonempty (Derivation b Delta (graph3 (TransparentChildFields.first V true) dest node code param))) :
    Nonempty (Derivation b Delta (graph3 (move n arity V) out node code param)) ↔
    Nonempty (Derivation b Delta (programGraph (OriginalHeadMove.headMove n arity) out ![f,base,g,dest,ss,ts])) := by
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse b alpha param ss ts) hp
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  let gs : Fin 6 → Program 3 := ![TransparentMetadataFields.head V false,TransparentChildFields.first V false,
    TransparentMetadataFields.head V true,TransparentChildFields.first V true,symbols,types]
  let ys : Fin 6 → OTerm alpha := ![f,base,g,dest,ss,ts]
  have hs : Nonempty (Derivation b Delta (programGraph symbols ss xs)) :=
    unaryValue InternalUnpair.left (.projection 2) ss param xs ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 2 xs)
  have ht : Nonempty (Derivation b Delta (programGraph types ts xs)) :=
    unaryValue InternalUnpair.right (.projection 2) ts param xs ⟨Derivation.conjunctionRight hi⟩ (projectionValue 2 xs)
  have hall : ∀ i, Nonempty (Derivation b Delta (programGraph (gs i) (ys i) xs)) := by
    intro i
    exact Fin.cases hf (Fin.cases hb (Fin.cases hg (Fin.cases hd (Fin.cases hs (Fin.cases ht (fun k => Fin.elim0 k)))))) i
  constructor
  · intro h
    have hc := successorBranchElim V (constant 3 0) (body n arity V) out (numeral 0) xs hV h
    exact compositionRecover (OriginalHeadMove.headMove n arity) gs out xs ys hc hall
  · intro h
    have hc := compositionValue (OriginalHeadMove.headMove n arity) gs out xs ys h hall
    exact successorBranchIntro V (constant 3 0) (body n arity V) out (numeral 0) xs hV hc

theorem ordinaryFirst (V : Program 3) (side : Bool) (node code param raw hd child : OTerm alpha)
    (hV : Nonempty (Derivation b Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation b Delta (graph3 (TransparentChildFields.rawCode side) raw node code param)))
    (hc : Nonempty (Derivation b Delta (graph2 ordinaryConstructor raw hd child))) :
    Nonempty (Derivation b Delta (graph3 (TransparentChildFields.first V side) child node code param)) := by
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ha := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryArity (TransparentChildFields.rawCode side) raw hd child xs hq hc
  have hf := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryFirst (TransparentChildFields.rawCode side) raw hd child xs hq hc
  have hu := successorBranchIntro (arityOf (TransparentChildFields.rawCode side)) (constant 3 0)
    (firstOf (TransparentChildFields.rawCode side)) child (numeral 0) xs ha hf
  exact TransparentChildFields.InternalProof.guarded V (TransparentChildFields.firstRaw side) child node code param hV hu

theorem internalOrdinary : Targets.InternalOrdinary := by
  intro n arity b alpha Delta V node code param source target f base g dest ss ts out hV hn hp hsource htarget
  obtain ⟨hqs,hqt⟩ := StructuralExchangeFields.SupportProof.rawSides node code param source target hn
  have hf := (TransparentMetadataFields.InternalProof.ordinaryFields V false node code param source f base hV hqs hsource).2.1
  have hg := (TransparentMetadataFields.InternalProof.ordinaryFields V true node code param target g dest hV hqt htarget).2.1
  exact factor n arity V node code param f base g dest ss ts out hV hp hf
    (ordinaryFirst V false node code param source f base hV hqs hsource) hg
    (ordinaryFirst V true node code param target g dest hV hqt htarget)

theorem numberedFirst (V : Program 3) (side : Bool) (node code param raw rank hd tau base ts extras : OTerm alpha)
    (hV : Nonempty (Derivation b Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation b Delta (graph3 (TransparentChildFields.rawCode side) raw node code param)))
    (hc : Nonempty (Derivation b Delta (programGraph numberedConstructor raw ![rank,hd,tau,base,ts,extras]))) :
    Nonempty (Derivation b Delta (graph3 (TransparentChildFields.first V side) base node code param)) := by
  let q := TransparentChildFields.rawCode side
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  exact (TransparentChildFields.InternalProof.binaryChildren V side node code param base extras hV
    (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedArity q raw rank hd tau base ts extras xs hq hc)
    (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedFirst q raw rank hd tau base ts extras xs hq hc)
    (OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedSecond q raw rank hd tau base ts extras xs hq hc)).1

theorem internalNumbered : Targets.InternalNumbered := by
  intro n arity b alpha Delta V node code param source target k f tau base ts extras l g rho dest us other ss tt out hV hn hp hsource htarget
  obtain ⟨hqs,hqt⟩ := StructuralExchangeFields.SupportProof.rawSides node code param source target hn
  have hf := (TransparentMetadataFields.InternalProof.numberedFields V false node code param source k f tau base ts extras hV hqs hsource).2.1
  have hg := (TransparentMetadataFields.InternalProof.numberedFields V true node code param target l g rho dest us other hV hqt htarget).2.1
  exact factor n arity V node code param f base g dest ss tt out hV hp hf
    (numberedFirst V false node code param source k f tau base ts extras hV hqs hsource) hg
    (numberedFirst V true node code param target l g rho dest us other hV hqt htarget)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadMoveFields.InternalProof
