module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallArgsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope
  (hopGood hopTarget hopSource hopWitness hopRawTarget)
open NumberedWindowInternalSparsePathEnvelopeTargets (hopCertified z suc)
open NumberedWindowInternalSparsePathAdvance
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
open NumberedWindowInternalSparsePathAdvanceOpenCallArgsProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev bothLeast (p : Program 3) := conjunction (fromMatches p) (toMatches p)
private abbrev allRaw (r : Program 5) (p : Program 3) :=
  conjunction (rawCall r) (bothLeast p)
private abbrev allHop (r : Program 5) (p : Program 3) :=
  conjunction (atHop hopGood) (allRaw r p)

theorem callsIntro (raw : Program 5) (p : Program 3) (c ty current hop target q w r : OTerm α)
    (owner : Nonempty (Derivation body Γ (hopCertified hop target q w r)))
    (ready : Nonempty (Derivation body Γ (actualCalls raw p c ty current target q w r))) :
    Nonempty (Derivation body Γ (acceptedGuard raw p c ty (suc current) hop)) := by
  let s := suc current
  let xs := coords c ty s hop
  have reports := liftReports c ty s hop target q w r owner
  obtain ⟨ready⟩ := ready
  have rawGood := rawIntro raw c ty s hop target q w r reports ⟨Derivation.conjunctionLeft ready⟩
  have src := leastIntro p hopSource c ty s hop q s reports.2.2.1
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight ready)⟩
  have dst := leastIntro p hopRawTarget c ty s hop r (suc target) reports.2.2.2.2
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight ready)⟩
  have srcMatch : At4 body Γ xs (fromMatches p) (suc z) :=
    matchIntro (leastCall p hopSource) (.projection 2) xs s src (projectionValue (2 : Fin 4) xs)
  have dstMatch : At4 body Γ xs (toMatches p) (suc z) :=
    matchIntro (leastCall p hopRawTarget) targetCode xs (suc target) dst
      (targetGraph target c ty s hop reports.2.1)
  have leastGood := conjunctionAccept (fromMatches p) (toMatches p) xs srcMatch dstMatch
  have sourceGood := conjunctionAccept (rawCall raw) (bothLeast p) xs rawGood leastGood
  have hopGood' := conjunctionAccept (atHop hopGood) (allRaw raw p) xs reports.1 sourceGood
  exact conjunctionAccept statePresent (allHop raw p) xs (stateSucc c ty current hop) hopGood'

theorem callsRead (raw : Program 5) (p : Program 3) (c ty current hop target q w r : OTerm α)
    (owner : Nonempty (Derivation body Γ (hopCertified hop target q w r)))
    (accepted : Nonempty (Derivation body Γ (acceptedGuard raw p c ty (suc current) hop))) :
    Nonempty (Derivation body Γ (actualCalls raw p c ty current target q w r)) := by
  let s := suc current
  let xs := coords c ty s hop
  have reports := liftReports c ty s hop target q w r owner
  obtain ⟨withHop⟩ := conjunctionRecover statePresent (allHop raw p) xs accepted
  obtain ⟨withRaw⟩ := conjunctionRecover (atHop hopGood) (allRaw raw p) xs
    ⟨Derivation.conjunctionRight withHop⟩
  obtain ⟨all⟩ := conjunctionRecover (rawCall raw) (bothLeast p) xs
    ⟨Derivation.conjunctionRight withRaw⟩
  obtain ⟨least⟩ := conjunctionRecover (fromMatches p) (toMatches p) xs
    ⟨Derivation.conjunctionRight all⟩
  have srcMatch := matchRead (leastCall p hopSource) (.projection 2) c ty s hop s
    ⟨Derivation.conjunctionLeft least⟩ (projectionValue (2 : Fin 4) xs)
  have dstMatch := matchRead (leastCall p hopRawTarget) targetCode c ty s hop (suc target)
    ⟨Derivation.conjunctionRight least⟩ (targetGraph target c ty s hop reports.2.1)
  obtain ⟨raw'⟩ := rawRead raw c ty s hop target q w r reports ⟨Derivation.conjunctionLeft all⟩
  obtain ⟨src⟩ := leastRead p hopSource c ty s hop q s reports.2.2.1 srcMatch
  obtain ⟨dst⟩ := leastRead p hopRawTarget c ty s hop r (suc target) reports.2.2.2.2 dstMatch
  exact ⟨Derivation.conjunctionIntroduction raw' (Derivation.conjunctionIntroduction src dst)⟩

theorem calls : OpenAdvanceCalls := by
  intro body raw p α c ty current hop target q w r
  let owner := hopCertified hop target q w r
  let a := acceptedGuard raw p c ty (suc current) hop
  let b := actualCalls raw p c ty current target q w r
  have oa : Derivation body [a,owner] owner :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have ob : Derivation body [b,owner] owner :=
    Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨forward⟩ := callsRead raw p c ty current hop target q w r
    ⟨oa⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := callsIntro raw p c ty current hop target q w r
    ⟨ob⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenCallsProof
