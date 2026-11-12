module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationControlProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open OriginalTransparentMixedPathInternalDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem hop (source : Program 2)
 (s t cert parameter childS childT childCert arg d e arrow state next : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)))
 (hs : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (hn : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert parameter))) :
 Nonempty (Derivation body Delta (graph1 (OriginalTransparentMixedPathDefinitions.transition source) next state)) := by
 have hf := OriginalTransparentMixedPathApplicationFieldsProof.applicationFields source
  s t cert parameter childS childT childCert arg d e arrow hh
 have htag := andLeft hf
 have hg := andLeft (andRight hf)
 have hfns := andLeft (andRight (andRight hf))
 have hfnt := andLeft (andRight (andRight (andRight hf)))
 have hcert := andRight (andRight (andRight (andRight hf)))
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let programs : Fin 4 → Program 4 :=
  ![OriginalTransparentApplicationFunctionDefinitions.sourceFunction,
    OriginalTransparentApplicationFunctionDefinitions.targetFunction,
    OriginalTransparentApplicationFunctionDefinitions.childCertificate,
    OriginalTransparentApplicationFunctionDefinitions.childParameter]
 have hselectors : ∀ i : Fin 4, Nonempty (Derivation body Delta
   (programGraph (programs i) (![childS,childT,childCert,parameter] i) xs)) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact hfns
  refine Fin.cases ?_ (fun i => ?_) i
  · exact hfnt
  refine Fin.cases ?_ (fun i => ?_) i
  · exact hcert
  refine Fin.cases ?_ (fun i => Fin.elim0 i) i
  exact projectionValue 3 xs
 have hchild := compositionValue OriginalHereditaryLambda.live programs next xs
  ![childS,childT,childCert,parameter] hn hselectors
 exact OriginalTransparentMixedPathApplicationControlProof.applicationAtLive source
  s t cert parameter state next htag hs hg hchild

theorem actualApplicationHop : OriginalTransparentMixedPathInternalTargets.ActualApplicationHop := by
 intro source body alpha Delta s t cert parameter childS childT childCert arg d e arrow state next
 apply Nonempty.intro
 apply Derivation.implicationIntroduction
 let A := ApplicationHop source s t cert parameter childS childT childCert arg d e arrow ⊓
   (graph4 OriginalHereditaryLambda.live state s t cert parameter ⊓
    graph4 OriginalHereditaryLambda.live next childS childT childCert parameter)
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact Classical.choice (hop source s t cert parameter childS childT childCert arg d e arrow state next
  (andLeft h) (andLeft (andRight h)) (andRight (andRight h)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationProof
