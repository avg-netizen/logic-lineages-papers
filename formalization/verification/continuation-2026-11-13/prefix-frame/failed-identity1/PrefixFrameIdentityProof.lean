module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionEqualityProof
open InternalTagArithmeticSyntaxProof (eqn z)
open InternalTagArithmeticSupportProof (refl symm)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PrefixFrameDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem binaryInputs (P : Program 2) (out a b a' b' : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (eqn a a')))
 (hb : Nonempty (Derivation body Delta (eqn b b')))
 (hp : Nonempty (Derivation body Delta (graph2 P out a b))) :
 Nonempty (Derivation body Delta (graph2 P out a' b')) := by
 apply graphInputTransport body alpha 2 Delta (OrdinaryArithmetic.graphFormula P)
   out (Fin.cons a (Fin.cons b Fin.elim0)) (Fin.cons a' (Fin.cons b' Fin.elim0)) _ hp
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
 · rw [onEquality]; exact ha
 · rw [onEquality]; exact hb

theorem identityCore (R : Program 2) (suffix old work input joined output : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (geometry z z suffix old work input joined output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output z input)) := by
 have hw := InternalApplicationValidityStackAppendListProof.appendZeroRecover work suffix (andLeft hg)
 have hj := InternalApplicationValidityStackAppendListProof.appendZeroRecover joined old (andLeft (andRight (andRight hg)))
 have hi := binaryInputs InternalPairing.pairing input work old suffix old hw ⟨refl old⟩ (andLeft (andRight hg))
 have ho := binaryInputs InternalPairing.pairing output suffix joined suffix old ⟨refl suffix⟩ hj (andRight (andRight (andRight hg)))
 have he := valueUnique InternalPairing.pairing input output (Fin.cons suffix (Fin.cons old Fin.elim0)) hi ho
 exact outputTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) input output
   (Fin.cons z (Fin.cons input Fin.elim0)) he
   (InternalNumericIterationSupportProof.repeatZeroValue (OriginalHereditaryCombinedStep.step R) input)

theorem actualIdentity : PrefixFrameTargets.ActualIdentity := by
 intro R body alpha Delta
 unfold PrefixFrame
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let old : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let work : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let input : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let output : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let A := geometry z z suffix old work input joined output
 obtain ⟨h⟩ := identityCore R (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
   suffix old work input joined output ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [frameBody,numeralRename] using Nonempty.intro (Derivation.implicationIntroduction h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
