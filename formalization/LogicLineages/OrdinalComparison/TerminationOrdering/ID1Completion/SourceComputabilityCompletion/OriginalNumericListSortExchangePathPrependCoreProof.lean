module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePrependProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionEqualityProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open OriginalNumericListSortExchange (edge)
open OriginalNumericListSortExchangePathPrepend
open OriginalNumericListSortExchangePathPrependInductionDefinitions OriginalNumericListSortExchangePathPrependSyntaxProof OriginalNumericListSortExchangePathPrependBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] mapPath entryLift edge

theorem rawTransport (source target raw other : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn raw other)))
 (hp : Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target raw))) :
 Nonempty (Derivation body Delta (InternalPathChecker.pathGraph edge source target other)) := by
 apply graphInputTransport body alpha 3 Delta _ (suc z)
   (Fin.cons source (Fin.cons target (Fin.cons raw Fin.elim0)))
   (Fin.cons source (Fin.cons target (Fin.cons other Fin.elim0))) _ hp
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl source⟩
 · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl target⟩
 · rw [onEquality]; exact he

theorem atZero (raw source target value newSource newTarget mapped : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields raw source target value newSource newTarget mapped))) :
 Nonempty (Derivation body Delta (result newSource newTarget mapped)) := by
 have hp := rawTransport source target raw z hz (andLeft hf)
 obtain ⟨he⟩ := InternalPathCheckerProof.nilRecover edge source target hp
 have hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode newSource value target)) := by
   apply graphInputTransport body alpha 2 Delta _ newSource
     (Fin.cons value (Fin.cons source Fin.elim0)) (Fin.cons value (Fin.cons target Fin.elim0)) _ (andLeft (andRight hf))
   intro i
   refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
   · rw [onEquality]; exact ⟨InternalTagArithmeticSupportProof.refl value⟩
   · rw [onEquality]; simpa only [equalEqn] using (Nonempty.intro he)
 have heNew := valueUnique InternalListCodec.consCode newSource newTarget (Fin.cons value (Fin.cons target Fin.elim0)) hs (andLeft (andRight (andRight hf)))
 have hm := headTransport mapPath mapped raw z (Fin.cons value Fin.elim0) hz (andRight (andRight (andRight hf)))
 obtain ⟨hmz⟩ := valueUnique mapPath mapped z (Fin.cons z (Fin.cons value Fin.elim0)) hm (OriginalNumericListSortExchangePathPrependRecursionProof.atZero value)
 have hnil := iffBackward (InternalPathCheckerProof.pathNil edge newSource newTarget)
   (by simpa only [equalEqn] using heNew)
 exact rawTransport newSource newTarget z mapped ⟨InternalTagArithmeticSupportProof.symm hmz⟩ hnil

theorem atCons (raw source target value newSource newTarget mapped oldEntry restCode : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw oldEntry restCode)))
 (hf : Nonempty (Derivation body Delta (fields raw source target value newSource newTarget mapped))) :
 Nonempty (Derivation body Delta (result newSource newTarget mapped)) := by
 let call (p : Program 2) : Program 3 := .composition p ![.projection 0,.projection 2]
 let tailCall : Program 3 := .composition mapPath ![.projection 1,.projection 2]
 let qs : Fin 9 → Program 3 := ![call vertex,call certificate,call oldFront,call payload,
   call newFront,call newCertificate,call newVertex,call entryLift,tailCall]
 let xs : Fin 3 → OTerm alpha := Fin.cons oldEntry (Fin.cons restCode (Fin.cons value Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j vals Theta hj hq
 rw [resultRename]
 have hv : (fun i : Fin 3 => (xs i).relabel j) =
   Fin.cons (oldEntry.relabel j) (Fin.cons (restCode.relabel j) (Fin.cons (value.relabel j) Fin.elim0)) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 let ys : Fin 3 → OTerm beta := Fin.cons (oldEntry.relabel j) (Fin.cons (restCode.relabel j) (Fin.cons (value.relabel j) Fin.elim0))
 have hq' (i : Fin 9) : Nonempty (Derivation body Theta (programGraph (qs i) (vals i) ys)) := by
   simpa only [hv,ys] using hq i
 have recover (p : Program 2) (out : OTerm beta)
   (hp : Nonempty (Derivation body Theta (programGraph (call p) out ys))) :
   Nonempty (Derivation body Theta (graph2 p out (oldEntry.relabel j) (value.relabel j))) :=
   binaryRecover p (.projection 0) (.projection 2) out (oldEntry.relabel j) (value.relabel j) ys hp
     (projectionValue 0 ys) (projectionValue 2 ys)
 have h0 : Nonempty (Derivation body Theta (graph2 vertex (vals 0) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover vertex (vals 0)
   have hselect : qs (0 : Fin 9) = call vertex := rfl
   simpa only [hselect] using hq' 0
 have h1 : Nonempty (Derivation body Theta (graph2 certificate (vals 1) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover certificate (vals 1)
   have hselect : qs (1 : Fin 9) = call certificate := rfl
   simpa only [hselect] using hq' 1
 have h2 : Nonempty (Derivation body Theta (graph2 oldFront (vals 2) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover oldFront (vals 2)
   have hselect : qs (2 : Fin 9) = call oldFront := rfl
   simpa only [hselect] using hq' 2
 have h3 : Nonempty (Derivation body Theta (graph2 payload (vals 3) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover payload (vals 3)
   have hselect : qs (3 : Fin 9) = call payload := rfl
   simpa only [hselect] using hq' 3
 have h4 : Nonempty (Derivation body Theta (graph2 newFront (vals 4) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover newFront (vals 4)
   have hselect : qs (4 : Fin 9) = call newFront := rfl
   simpa only [hselect] using hq' 4
 have h5 : Nonempty (Derivation body Theta (graph2 newCertificate (vals 5) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover newCertificate (vals 5)
   have hselect : qs (5 : Fin 9) = call newCertificate := rfl
   simpa only [hselect] using hq' 5
 have h6 : Nonempty (Derivation body Theta (graph2 newVertex (vals 6) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover newVertex (vals 6)
   have hselect : qs (6 : Fin 9) = call newVertex := rfl
   simpa only [hselect] using hq' 6
 have h7 : Nonempty (Derivation body Theta (graph2 entryLift (vals 7) (oldEntry.relabel j) (value.relabel j))) := by
   apply recover entryLift (vals 7)
   have hselect : qs (7 : Fin 9) = call entryLift := rfl
   simpa only [hselect] using hq' 7
 have h8 : Nonempty (Derivation body Theta (graph2 mapPath (vals 8) (restCode.relabel j) (value.relabel j))) := by
   apply binaryRecover mapPath (.projection 1) (.projection 2) (vals 8) (restCode.relabel j) (value.relabel j) ys _ (projectionValue 1 ys) (projectionValue 2 ys)
   have hselect : qs (8 : Fin 9) = tailCall := rfl
   simpa only [hselect] using hq' 8
 let zs : Fin 2 → OTerm beta := Fin.cons (oldEntry.relabel j) (Fin.cons (value.relabel j) Fin.elim0)
 have hentry := reconstructPair (oldEntry.relabel j) (vals 0) (vals 1)
   (unaryRecover InternalUnpair.left (.projection 0) (vals 0) (oldEntry.relabel j) zs h0 (projectionValue 0 zs))
   (unaryRecover InternalUnpair.right (.projection 0) (vals 1) (oldEntry.relabel j) zs h1 (projectionValue 0 zs))
 have hcert := reconstructPair (vals 1) (vals 2) (vals 3)
   (unaryRecover InternalUnpair.left certificate (vals 2) (vals 1) zs h2 h1)
   (unaryRecover InternalUnpair.right certificate (vals 3) (vals 1) zs h3 h1)
 have hfront := binaryRecover InternalListCodec.consCode (.projection 1) oldFront (vals 4) (value.relabel j) (vals 2) zs h4 (projectionValue 1 zs) h2
 have hnewcert := binaryRecover InternalPairing.pairing newFront payload (vals 5) (vals 4) (vals 3) zs h5 h4 h3
 have hvertex := binaryRecover InternalListCodec.consCode (.projection 1) vertex (vals 6) (value.relabel j) (vals 0) zs h6 (projectionValue 1 zs) h0
 have hnewentry := binaryRecover InternalPairing.pairing newVertex newCertificate (vals 7) (vals 6) (vals 5) zs (by simpa only [entryLift,pairOf] using h7) h6 h5
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have hf' := renameInto hf j Theta hj
 simp only [fields,InternalPathChecker.pathGraph,InternalPathChecker.checkerGraph,InternalPathChecker.triple,
   conjunctionRename,graph2Rename,programRename,consTermRename,emptyRename,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hf'
 have oldParts := iffForward (InternalPathCheckerProof.pathCons edge (source.relabel j) (target.relabel j) (raw.relabel j)
   (oldEntry.relabel j) (restCode.relabel j) (vals 0) (vals 1) hentry hc') (andLeft hf')
 have newEdge := OriginalNumericListSortExchangePrependProof.prepend (source.relabel j) (vals 0) (vals 1)
   (vals 2) (vals 3) (value.relabel j) (vals 4) (vals 5) (newSource.relabel j) (vals 6)
   (andLeft oldParts) hcert hfront hnewcert (andLeft (andRight hf')) hvertex
 have newTail := belowRawApply (raw.relabel j) (restCode.relabel j) (vals 0) (target.relabel j)
   (value.relabel j) (vals 6) (newTarget.relabel j) (vals 8) hi'
   (InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (oldEntry.relabel j) (restCode.relabel j) hc')
   (andIntro (andRight oldParts) (andIntro hvertex (andIntro (andLeft (andRight (andRight hf'))) h8)))
 have hnewcons := OriginalNumericListSortExchangePathPrependRecursionProof.consForward (raw.relabel j) (oldEntry.relabel j) (restCode.relabel j)
   (value.relabel j) (vals 7) (vals 8) (mapped.relabel j) hc' h7 h8 (andRight (andRight (andRight hf')))
 exact iffBackward (InternalPathCheckerProof.pathCons edge (newSource.relabel j) (newTarget.relabel j) (mapped.relabel j)
   (vals 7) (vals 8) (vals 6) (vals 5) hnewentry hnewcons) (andIntro newEdge newTail)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependCoreProof
