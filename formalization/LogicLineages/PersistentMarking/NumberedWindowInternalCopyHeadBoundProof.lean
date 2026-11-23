module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadBoundProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanEvaluationProof (exactLessThanEvaluation)
open ID1Completion.InternalLessThanProof (lessOfAcceptance)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowCopyAlgorithm (Entries lookup rankParts rank)
open NumberedWindowPairAlgorithm (decode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumeralGraphChecks (exact_NumeralGraph)
open NumberedWindowNumeralGraphTargets (inputs)
open NumberedWindowInternalCopyHeadBoundTargets

attribute [local irreducible] programGraph

private theorem lookupBound (entries : Entries) (name arity index : Nat)
    (h : lookup entries name = some (arity,index)) : index < entries.length := by
  induction entries generalizing arity index with
  | nil => cases h
  | cons row tail ih =>
    change (if name = row.1 then some (row.2,0)
      else (lookup tail name).map (fun p => (p.1,p.2+1))) = some (arity,index) at h
    by_cases hit : name = row.1
    · rw [if_pos hit] at h
      have same : 0 = index := congrArg Prod.snd (Option.some.inj h)
      rw [← same, List.length_cons]
      exact Nat.zero_lt_succ tail.length
    · rw [if_neg hit] at h
      cases htail : lookup tail name with
      | none => simp [htail] at h
      | some p =>
        obtain ⟨va,vi⟩ := p
        have original := ih va vi htail
        have same : vi + 1 = index := by
          have eq : (va, vi+1) = (arity,index) := by simpa only [htail,Option.map_some,Option.some.injEq] using h
          exact congrArg Prod.snd eq
        rw [← same, List.length_cons]
        exact Nat.succ_lt_succ original

private theorem partsBound (entries : Entries) (tag payload output : Nat)
    (found : rankParts entries tag payload = some output) :
    output < entries.length + 2 := by
  unfold rankParts at found
  by_cases builtin : tag < 4
  · rw [if_pos builtin] at found
    have v := Option.some.inj found
    omega
  · rw [if_neg builtin] at found
    by_cases app : tag = 4
    · rw [if_pos app] at found
      have v := Option.some.inj found
      omega
    · rw [if_neg app] at found
      by_cases ranked : tag = 5
      · rw [if_pos ranked] at found
        cases decoded : decode payload with
        | none => simp [decoded] at found
        | some p =>
          obtain ⟨name,arity⟩ := p
          cases read : lookup entries name with
          | none => simp [decoded,read] at found
          | some q =>
            obtain ⟨declared,index⟩ := q
            by_cases exactArity : arity = declared
            · have equal : index + 2 = output := by simpa [decoded,read,exactArity] using found
              have small := lookupBound entries name declared index read
              omega
            · simp [decoded,read,exactArity] at found
      · simp [ranked] at found

theorem exact_OriginalFiniteCopyHeadRank : ExactOriginalFiniteCopyHeadRank := by
  intro entries head value observed
  unfold rank at observed
  cases d : decode head with
  | none => simp [d] at observed
  | some p =>
    obtain ⟨tag, payload⟩ := p
    exact partsBound entries tag payload value (by simpa [d] using observed)

theorem exact_OriginalObjectFiniteCopyHeadRank : ExactOriginalObjectFiniteCopyHeadRank := by
  intro entries head value B α Γ observed
  have bound := exact_OriginalFiniteCopyHeadRank entries head value observed
  let n := entries.length + 2
  let xs := value ::ᵥ n ::ᵥ List.Vector.nil
  have d := exact_NumeralGraph 2 ltTest xs B α Γ
  have arguments : (inputs xs : Fin 2 → OTerm α) =
      Fin.cons (numeral value) (Fin.cons (numeral n) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  have observedOne : evaluate ltTest xs = 1 := by
    change evaluate ltTest (value ::ᵥ n ::ᵥ List.Vector.nil) = 1
    rw [exactLessThanEvaluation,if_pos bound]
  rw [arguments,observedOne] at d
  exact lessOfAcceptance (numeral value) (numeral n) d

#print axioms exact_OriginalFiniteCopyHeadRank
#print axioms exact_OriginalObjectFiniteCopyHeadRank

end LogicLineages.PersistentMarking.NumberedWindowInternalCopyHeadBoundProof
