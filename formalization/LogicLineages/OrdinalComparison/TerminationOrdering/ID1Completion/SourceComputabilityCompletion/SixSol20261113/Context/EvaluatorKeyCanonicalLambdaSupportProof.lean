module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyDomainClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalLambdaTraversalInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem alignFields (parent parameter ld lc child lp rd rc rp : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (LambdaFields parent rd rc child parameter rp)))
 (hd : Nonempty (Derivation body Delta (equal ld rd)))
 (hc : Nonempty (Derivation body Delta (equal lc rc)))
 (hp : Nonempty (Derivation body Delta (equal lp rp))) :
 Nonempty (Derivation body Delta (LambdaFields parent ld lc child parameter lp)) := by
 have hdq := (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn ld rd)).mp hd
 have hcq := (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn lc rc)).mp hc
 have hpq := (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn lp rp)).mp hp
 obtain ⟨hdq⟩ := hdq
 obtain ⟨hcq⟩ := hcq
 obtain ⟨hpq⟩ := hpq
 exact andIntro (andLeft hf) (andIntro
   (outputTransport OriginalLambdaTraversal.rawDomain rd ld ![parent] ⟨symm hdq⟩ (andLeft (andRight hf)))
   (andIntro (outputTransport OriginalLambdaTraversal.rawCodomain rc lc ![parent] ⟨symm hcq⟩ (andLeft (andRight (andRight hf))))
     (andIntro (andLeft (andRight (andRight (andRight hf))))
       (outputTransport OriginalLambdaTraversal.childParameter rp lp ![parent,parameter] ⟨symm hpq⟩ (andRight (andRight (andRight (andRight hf))))))))
theorem rebuilt (domain codomain child otherChild out otherOut : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal child otherChild)))
 (hl : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out domain codomain child)))
 (hr : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor otherOut domain codomain otherChild))) :
 Nonempty (Derivation body Delta (equal out otherOut)) := by
 have hh : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out domain codomain otherChild)) := by
   simp only [graph3,programGraph] at hl ⊢
   apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Delta
     (OrdinaryArithmetic.graphFormula OriginalLambdaConstructor.constructor) out
     (![domain,codomain,child]) (![domain,codomain,otherChild]) _ hl
   intro i
   have hd : Nonempty (Derivation body Delta (equal domain domain)) := by
     rw [equalEqn]; exact ⟨refl domain⟩
   have hc : Nonempty (Derivation body Delta (equal codomain codomain)) := by
     rw [equalEqn]; exact ⟨refl codomain⟩
   exact Fin.cases hd (Fin.cases hc (Fin.cases he (fun k => Fin.elim0 k))) i
 have hq := valueUnique OriginalLambdaConstructor.constructor out otherOut ![domain,codomain,otherChild] hh hr
 exact (congrArg (fun f => Nonempty (Derivation body Delta f)) (equalEqn out otherOut)).mpr hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaSupportProof
