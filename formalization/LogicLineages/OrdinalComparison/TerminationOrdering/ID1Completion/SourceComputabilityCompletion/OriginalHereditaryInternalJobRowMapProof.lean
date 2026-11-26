module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalAgendaTransportProof
open OriginalHereditaryInternalJobRow OriginalHereditaryInternalJobRowSyntaxProof
open OriginalHereditaryInternalJobRowMapSyntaxProof
open OriginalHereditaryAgendaPotentialTaggedHelpersProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalListInduction InternalListInductionSyntaxProof InternalListInductionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem nilCore (H : Program 1) (M W : Program 2) (c B tagged : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged z))) :
 Nonempty (Derivation body Delta (Agenda H M W c B tagged)) := by
 have he := valueUnique OriginalHereditaryVisitScheduler.tagVisits z tagged (Fin.cons z Fin.elim0) tagNil ht
 exact agendaTransport H M W c B z tagged (by simpa only [equalEqn] using he)
  (OriginalHereditaryInternalAgendaStructuralProof.nil H M W c B)

theorem consCore (H : Program 1) (M W : Program 2) (row head tail c B tagged : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph row head tail)))
 (ih : Nonempty (Derivation body Delta (mapRow H M W tail)))
 (hj : Nonempty (Derivation body Delta (Jobs H M W c B row)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged row))) :
 Nonempty (Derivation body Delta (Agenda H M W c B tagged)) := by
 have hh := OriginalHereditaryInternalJobRowStructuralProof.head H M W c B row head tail hj hc
 have htail := OriginalHereditaryInternalJobRowStructuralProof.tail H M W c B row head tail hj hc
 let tp : Program 2 := .composition OriginalHereditaryVisitScheduler.tagVisits (fun _ : Fin 1 => .projection 1)
 let vp : Program 2 := pairOf (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
 let qs : Fin 2 → Program 2 := ![tp,vp]
 let xs : Fin 2 → OTerm alpha := ![head,tail]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![head.relabel j,tail.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hc' := renameInto hc j Theta hinc
 have ih' := renameInto ih j Theta hinc
 have hh' := renameInto hh j Theta hinc
 have htail' := renameInto htail j Theta hinc
 have ht' := renameInto ht j Theta hinc
 simp only [consGraphRename,mapRowRename,jobRename,jobsRename,graph1Rename] at hc' ih' hh' htail' ht'
 have hmap := InternalApplicationCertificateConstructorsSupportProof.unaryRecover OriginalHereditaryVisitScheduler.tagVisits (.projection 1)
  (ys 0) (tail.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hv := InternalApplicationCertificateConstructorsSupportProof.binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 2 0) (.projection 0)
  (ys 1) z (head.relabel j) xx (hq 1) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx) (projectionValue 0 xx)
 have hcons := tagCons (row.relabel j) (head.relabel j) (tail.relabel j) (tagged.relabel j) (ys 1) (ys 0) hc' hv hmap ht'
 have hgood := mapApply H M W (tail.relabel j) (c.relabel j) (B.relabel j) (ys 0) ih' (andIntro htail' hmap)
 rw [agendaRename]
 exact OriginalHereditaryInternalAgendaStructuralProof.cons H M W (c.relabel j) (B.relabel j)
  (tagged.relabel j) (ys 1) (ys 0) hcons
  (OriginalHereditaryInternalAgendaStructuralProof.visitFrame H M W (c.relabel j) (B.relabel j) (ys 1) (head.relabel j) hv hh') hgood
theorem zeroRow (H : Program 1) (M W : Program 2) :
 Nonempty (Derivation body Delta (mapRow H M W z)) := by
 unfold mapRow
 apply actualFiniteUniversalIntroduction body alpha 3 Delta
 let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let B : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let tagged : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := mapFields H M W (z.relabel Sum.inl) c B tagged
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
  intro f hf
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := nilCore H M W c B tagged (by simpa only [zRelabel] using andRight h)
 exact ⟨Derivation.implicationIntroduction h⟩
theorem consRow (H : Program 1) (M W : Program 2) (row head tail : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph row head tail)))
 (ih : Nonempty (Derivation body Delta (mapRow H M W tail))) :
 Nonempty (Derivation body Delta (mapRow H M W row)) := by
 unfold mapRow
 apply actualFiniteUniversalIntroduction body alpha 3 Delta
 let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let B : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let tagged : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := mapFields H M W (row.relabel Sum.inl) c B tagged
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
  intro f hf
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have h : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hc' := renameInto hc Sum.inl Theta inc
 have ih' := renameInto ih Sum.inl Theta inc
 rw [consGraphRename] at hc'
 rw [mapRowRename] at ih'
 obtain ⟨h⟩ := consCore H M W (row.relabel Sum.inl) (head.relabel Sum.inl) (tail.relabel Sum.inl) c B tagged hc' ih' (andLeft h) (andRight h)
 exact ⟨Derivation.implicationIntroduction h⟩
theorem allRows (H : Program 1) (M W : Program 2) (row : OTerm alpha) :
 Nonempty (Derivation body Delta (mapRow H M W row)) := by
 let theta : Formula (alpha ⊕ Fin 1) := mapRow H M W (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (atCode theta z)) := by
  rw [mapAtCode]
  exact zeroRow H M W
 have hs : Nonempty (Derivation body Delta (constructors theta)) := by
  unfold constructors
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  simp only [constructorBody,theta,mapAtIndex]
  let code : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let head : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let tail : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph code head tail
  let IH := mapRow H M W tail
  obtain ⟨d⟩ := consRow (body:=body) (Delta:=IH :: C :: Delta.map (fun f => f.relabel Sum.inl)) H M W code head tail
   ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
   ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
 have h := actualOriginalListInductionAtCode body alpha Delta theta row (andIntro hz hs)
 rw [mapAtCode] at h
 exact h
theorem actualTagged : OriginalHereditaryInternalJobRowTargets.Tagged := by
 intro body alpha Delta H M W c B row tagged hj ht
 exact mapApply H M W row c B tagged (allRows H M W row) (andIntro hj ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowMapProof
