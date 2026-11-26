module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionLengthProof (nonzeroCases)
open OriginalHereditaryDeletionRowsPrefixSyntaxProof
open OriginalHereditaryDeletionRowsPrefixLookupCoreProof
open OriginalAllPositionContextDeleteInductionCoreProof (contextNonzero)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (count front suffix out value : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields count front z suffix out value))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value z out)) := by
 apply nonzeroCases front _ (contextNonzero count front z (andLeft hf) (andLeft (andRight hf)))
 intro beta rho Theta head tail hrho hc
 simp only [graph2Rename,zRelabel]
 have hf' := renameInto hf rho Theta hrho
 simp only [fieldsRename,zRelabel] at hf'
 exact zeroAtCons (count.relabel rho) (front.relabel rho) head tail (suffix.relabel rho) (out.relabel rho) (value.relabel rho) hc hf'

theorem succCore (count front cutoff suffix out value : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row cutoff)))
 (hf : Nonempty (Derivation body Delta (fields count front (suc cutoff) suffix out value))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (suc cutoff) out)) := by
 apply nonzeroCases front _ (contextNonzero count front (suc cutoff) (andLeft hf) (andLeft (andRight hf)))
 intro beta rho Theta head tail hrho hc
 simp only [graph2Rename,sucRelabel]
 have hf' := renameInto hf rho Theta hrho
 simp only [fieldsRename,sucRelabel] at hf'
 have hi := renameInto hrow rho Theta hrho
 rw [rowRename] at hi
 exact successorAtCons (count.relabel rho) (front.relabel rho) (cutoff.relabel rho) head tail (suffix.relabel rho) (out.relabel rho) (value.relabel rho) hi hc hf'

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let count : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let front : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let suffix : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let A := fields count front z suffix out value
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
 obtain ⟨h⟩ := zeroCore count front suffix out value (body := body) (Delta := Theta) ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (cutoff : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row cutoff))) : Nonempty (Derivation body Delta (row (suc cutoff))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let count : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let front : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let suffix : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let c := cutoff.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
 let A := fields count front (suc c) suffix out value
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
 have hi := renameInto hrow Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi
 obtain ⟨h⟩ := succCore count front c suffix out value (body := body) (Delta := Theta) hi ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (cutoff : OTerm alpha) : Nonempty (Derivation body Delta (row cutoff)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb cutoff) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem prefixLookup (count front cutoff suffix out value : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
 (hb : Nonempty (Derivation body Delta (Below cutoff count)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front suffix)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff front))) :
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff out)) :=
 rowApply count front cutoff suffix out value (allRows cutoff) (andIntro hl (andIntro hb (andIntro ha hv)))

theorem exactPrefix : OriginalHereditaryDeletionRowsPrefixLookupTargets.PrefixLookup := by
 intro body alpha Delta count front cutoff suffix out value
 let A := fields count front cutoff suffix out value
 obtain ⟨h⟩ := rowApply count front cutoff suffix out value
   (allRows (body := body) (Delta := A :: Delta) cutoff) ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
