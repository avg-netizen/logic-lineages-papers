module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open InternalApplicationResultStackCompositionStateProof (liveOfValue)
open InternalApplicationResultStackComposition (liveState)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev visitFrame : Program 2 := visitOf (.projection 0) (.projection 1)
abbrev applicationFrame : Program 2 := applicationReturnOf (.projection 0) (.projection 1)
abbrev lambdaFrame : Program 2 := lambdaReturnOf (.projection 0) (.projection 1)

theorem liveOfRecover {n : Nat} (p q : Program n) (out work results : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (programGraph (liveOf p q) out xs)))
    (hp : Nonempty (Derivation positive Delta (programGraph p work xs)))
    (hq : Nonempty (Derivation positive Delta (programGraph q results xs))) :
    Nonempty (Derivation positive Delta (graph2 liveState out work results)) := by
  have h : Substitutes ![p,q] liveState (liveOf p q) :=
    liveSubstitution (.projection 0) (.projection 1)
  exact (substitutionGraph h ![work,results] xs out
    (fun i => Fin.cases hp (Fin.cases hq (fun j => Fin.elim0 j)) i)).mpr hs

theorem visitOfValue {n : Nat} (p q : Program n) (out value parameter : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph2 visitFrame out value parameter)))
    (hp : Nonempty (Derivation positive Delta (programGraph p value xs)))
    (hq : Nonempty (Derivation positive Delta (programGraph q parameter xs))) :
    Nonempty (Derivation positive Delta (programGraph (visitOf p q) out xs)) := by
  exact (substitutionGraph (visitSubstitution (gs := ![p,q]) (.projection 0) (.projection 1))
    ![value,parameter] xs out
    (fun i => Fin.cases hp (Fin.cases hq (fun j => Fin.elim0 j)) i)).mp hs

theorem applicationFrameValue {n : Nat} (p q : Program n) (out d e : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph2 applicationFrame out d e)))
    (hp : Nonempty (Derivation positive Delta (programGraph p d xs)))
    (hq : Nonempty (Derivation positive Delta (programGraph q e xs))) :
    Nonempty (Derivation positive Delta (programGraph (applicationReturnOf p q) out xs)) := by
  exact (substitutionGraph (applicationReturnSubstitution (gs := ![p,q]) (.projection 0) (.projection 1))
    ![d,e] xs out
    (fun i => Fin.cases hp (Fin.cases hq (fun j => Fin.elim0 j)) i)).mp hs

theorem lambdaFrameValue {n : Nat} (p q : Program n) (out d e : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph2 lambdaFrame out d e)))
    (hp : Nonempty (Derivation positive Delta (programGraph p d xs)))
    (hq : Nonempty (Derivation positive Delta (programGraph q e xs))) :
    Nonempty (Derivation positive Delta (programGraph (lambdaReturnOf p q) out xs)) := by
  exact (substitutionGraph (lambdaReturnSubstitution (gs := ![p,q]) (.projection 0) (.projection 1))
    ![d,e] xs out
    (fun i => Fin.cases hp (Fin.cases hq (fun j => Fin.elim0 j)) i)).mp hs

theorem visitValue (state value parameter suffix stack frame codedWork : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph2 visitFrame frame value parameter)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedWork frame suffix)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state codedWork stack))) :
    Nonempty (Derivation positive Delta (graph4 visitState state value parameter suffix stack)) := by
  let xs : Fin 4 → OTerm alpha := ![value,parameter,suffix,stack]
  exact liveOfValue _ _ state codedWork stack xs hs
    (binaryValue InternalListCodec.consCode _ _ codedWork frame suffix xs hw
      (visitOfValue _ _ frame value parameter xs hf (projectionValue 0 xs) (projectionValue 1 xs))
      (projectionValue 2 xs)) (projectionValue 3 xs)

theorem returnValue (state value suffix stack codedStack : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedStack value stack)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state suffix codedStack))) :
    Nonempty (Derivation positive Delta (graph3 returnState state value suffix stack)) := by
  let xs : Fin 3 → OTerm alpha := ![value,suffix,stack]
  exact liveOfValue _ _ state suffix codedStack xs hs (projectionValue 1 xs)
    (binaryValue InternalListCodec.consCode _ _ codedStack value stack xs hr
      (projectionValue 0 xs) (projectionValue 2 xs))

theorem applicationReturnValue (state d e suffix arg fn stack frame codedWork fnStack argStack : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph2 applicationFrame frame d e)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedWork frame suffix)))
    (hfn : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode fnStack fn stack)))
    (ha : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode argStack arg fnStack)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state codedWork argStack))) :
    Nonempty (Derivation positive Delta (programGraph applicationReturnState state ![d,e,suffix,arg,fn,stack])) := by
  let xs : Fin 6 → OTerm alpha := ![d,e,suffix,arg,fn,stack]
  exact liveOfValue _ _ state codedWork argStack xs hs
    (binaryValue InternalListCodec.consCode _ _ codedWork frame suffix xs hw
      (applicationFrameValue _ _ frame d e xs hf (projectionValue 0 xs) (projectionValue 1 xs))
      (projectionValue 2 xs))
    (binaryValue InternalListCodec.consCode _ _ argStack arg fnStack xs ha
      (projectionValue 3 xs)
      (binaryValue InternalListCodec.consCode _ _ fnStack fn stack xs hfn
        (projectionValue 4 xs) (projectionValue 5 xs)))

theorem lambdaReturnValue (state d e suffix body stack frame codedWork codedStack : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph2 lambdaFrame frame d e)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedWork frame suffix)))
    (hr : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedStack body stack)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state codedWork codedStack))) :
    Nonempty (Derivation positive Delta (programGraph lambdaReturnState state ![d,e,suffix,body,stack])) := by
  let xs : Fin 5 → OTerm alpha := ![d,e,suffix,body,stack]
  exact liveOfValue _ _ state codedWork codedStack xs hs
    (binaryValue InternalListCodec.consCode _ _ codedWork frame suffix xs hw
      (lambdaFrameValue _ _ frame d e xs hf (projectionValue 0 xs) (projectionValue 1 xs))
      (projectionValue 2 xs))
    (binaryValue InternalListCodec.consCode _ _ codedStack body stack xs hr
      (projectionValue 3 xs) (projectionValue 4 xs))

theorem applicationExpandedValue
    (state value parameter suffix stack d e fn arg frame fnFrame argFrame workRet workArg workFn : OTerm alpha)
    (hfields : Nonempty (Derivation positive Delta (ApplicationFields value d e fn arg)))
    (hf : Nonempty (Derivation positive Delta (graph2 applicationFrame frame d e)))
    (hff : Nonempty (Derivation positive Delta (graph2 visitFrame fnFrame fn parameter)))
    (haf : Nonempty (Derivation positive Delta (graph2 visitFrame argFrame arg parameter)))
    (hr : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode workRet frame suffix)))
    (ha : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode workArg argFrame workRet)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode workFn fnFrame workArg)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state workFn stack))) :
    Nonempty (Derivation positive Delta (graph4 applicationExpandedState state value parameter suffix stack)) := by
  let xs : Fin 4 → OTerm alpha := ![value,parameter,suffix,stack]
  have hd := unaryValue rawDomain (.projection 0) d value xs
    (andLeft (andRight hfields)) (projectionValue 0 xs)
  have he := unaryValue rawType (.projection 0) e value xs
    (andLeft (andRight (andRight hfields))) (projectionValue 0 xs)
  have hfn := unaryValue rawFunction (.projection 0) fn value xs
    (andLeft (andRight (andRight (andRight hfields)))) (projectionValue 0 xs)
  have harg := unaryValue rawArgument (.projection 0) arg value xs
    (andRight (andRight (andRight (andRight hfields)))) (projectionValue 0 xs)
  exact liveOfValue _ _ state workFn stack xs hs
    (binaryValue InternalListCodec.consCode _ _ workFn fnFrame workArg xs hw
      (visitOfValue _ _ fnFrame fn parameter xs hff hfn (projectionValue 1 xs))
      (binaryValue InternalListCodec.consCode _ _ workArg argFrame workRet xs ha
        (visitOfValue _ _ argFrame arg parameter xs haf harg (projectionValue 1 xs))
        (binaryValue InternalListCodec.consCode _ _ workRet frame suffix xs hr
          (applicationFrameValue _ _ frame d e xs hf hd he) (projectionValue 2 xs))))
    (projectionValue 3 xs)

theorem lambdaExpandedValue
    (state value parameter suffix stack d e body bodyParameter frame bodyFrame workRet workBody : OTerm alpha)
    (hfields : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hf : Nonempty (Derivation positive Delta (graph2 lambdaFrame frame d e)))
    (hbf : Nonempty (Derivation positive Delta (graph2 visitFrame bodyFrame body bodyParameter)))
    (hr : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode workRet frame suffix)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode workBody bodyFrame workRet)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state workBody stack))) :
    Nonempty (Derivation positive Delta (graph4 lambdaExpandedState state value parameter suffix stack)) := by
  let xs : Fin 4 → OTerm alpha := ![value,parameter,suffix,stack]
  have hd := unaryValue rawDomain (.projection 0) d value xs
    (andLeft (andRight hfields)) (projectionValue 0 xs)
  have he := unaryValue rawCodomain (.projection 0) e value xs
    (andLeft (andRight (andRight hfields))) (projectionValue 0 xs)
  have hb := unaryValue rawBody (.projection 0) body value xs
    (andLeft (andRight (andRight (andRight hfields)))) (projectionValue 0 xs)
  have hp := binaryValue childParameter (.projection 0) (.projection 1) bodyParameter value parameter xs
    (andRight (andRight (andRight (andRight hfields)))) (projectionValue 0 xs) (projectionValue 1 xs)
  exact liveOfValue _ _ state workBody stack xs hs
    (binaryValue InternalListCodec.consCode _ _ workBody bodyFrame workRet xs hw
      (visitOfValue _ _ bodyFrame body bodyParameter xs hbf hb hp)
      (binaryValue InternalListCodec.consCode _ _ workRet frame suffix xs hr
        (lambdaFrameValue _ _ frame d e xs hf hd he) (projectionValue 2 xs)))
    (projectionValue 3 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorStateProof
