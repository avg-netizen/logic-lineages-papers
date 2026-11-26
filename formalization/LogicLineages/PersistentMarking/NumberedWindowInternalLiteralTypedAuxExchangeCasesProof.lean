module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericLeastEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastHeaderInvarianceProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowAuxExchangeLiftTypingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxExchangeCasesProof
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowScalarAlgorithm (Settings admitted edge vertices least)
open NumberedWindowAnnotationAlgorithm (arrow annotations)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowExchangeAlgorithm (bits row)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView rowAuxPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowAuxExchangeLiftTypingProof (admissionAux)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (header exact_LiteralScalarEdgeHeader roundsInvariant)
open NumberedWindowInternalLiteralNumericLeastEdgeProof (exact_LiteralNumericLeastEdge)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast)
open NumberedWindowClassAlgorithm (rounds)

open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalLiteralLeastAuxPhysicalProfileProof
  (physicalAuxProfile exact_LiteralScalarEdgePhysicalAuxProfile)

private theorem typedNeedsSyntax (s : Settings) (ctx : List Nat) (ty x : Nat)
    (h : admitted s ctx ty x = true) : (syntaxBits x).1 = true := by
  simp only [admitted,NumberedWindowLexicalAlgorithm.typed,Bool.and_eq_true] at h
  exact h.1.1.1

private theorem exactFields (q : Nat) (fs : List Nat)
    (valid : (syntaxBits q).1 = true) (h : unpackNode q = some (6,fs)) :
    ∃ d c f a, fs = [d,c,f,a] ∧ q = auxRaw d c f a := by
  simp only [syntaxBits,NumberedWindowSyntaxAlgorithm.termNext,h,Option.any_some] at valid
  rcases fs with _ | ⟨d,_ | ⟨c,_ | ⟨f,_ | ⟨a,_ | ⟨x,xs⟩⟩⟩⟩⟩ <;>
    simp [NumberedWindowSyntaxAlgorithm.termParts] at valid
  exact ⟨d,c,f,a,rfl,codeOfNode h⟩

private theorem resultType (s : Settings) (ctx : List Nat) (ty d c f a : Nat)
    (h : admitted s ctx ty (auxRaw d c f a) = true) : c = ty := by
  have annotation : (annotations (auxRaw d c f a)).1 = c := by
    simp [annotations,NumberedWindowAnnotationAlgorithm.termNext,auxView,NumberedWindowAnnotationAlgorithm.termParts]
  simp only [admitted,NumberedWindowLexicalAlgorithm.typed,Bool.and_eq_true,beq_iff_eq,annotation] at h
  exact h.1.1.2

private theorem moveChild (s : Settings) (ctx : List Nat) (ty a b : Nat)
    (ha : admitted s ctx ty a = true) (hb : admitted s ctx ty b = true)
    (moved : (row s.equivalentHeads a b).1 = true) :
    edge s ctx ty a b = true := by
  have one := typedNeedsSyntax s ctx ty a ha
  have two := typedNeedsSyntax s ctx ty b hb
  simp [edge,bits,ha,hb,one,two,moved]

/-- A genuine typed tag-six scalar exchange has one smaller real
typed child edge and one unchanged raw coordinate. This is the
native numerical decomposition of the original table, not a change
to the application reduction relation or an open formula transfer. -/
theorem exact_LiteralTypedAuxExchangeCases (s : Settings) (ctx : List Nat)
    (ty q r dom cod fn arg : Nat) (edgeHeld : edge s ctx ty q r = true)
    (source : unpackNode q = some (6,[dom,cod,fn,arg])) :
    cod = ty ∧ ∃ f' a', unpackNode r = some (6,[dom,cod,f',a']) ∧
      ((edge s ctx (arrow dom cod) fn f' = true ∧ arg = a') ∨
       (fn = f' ∧ edge s ctx dom arg a' = true)) := by
  have same := exact_LiteralScalarEdgeHeader s ctx ty q r edgeHeld
  have w : admitted s ctx ty q = true ∧ admitted s ctx ty r = true := by
    simp only [edge,Bool.and_eq_true] at edgeHeld
    exact ⟨edgeHeld.1.2,edgeHeld.2⟩
  have valid := typedNeedsSyntax s ctx ty r w.2
  cases target : unpackNode r with
  | none => simp [header,source,target] at same
  | some node =>
    obtain ⟨tag,fs⟩ := node
    have h : tag = 6 := by
      simpa [header,source,target,eq_comm] using same
    subst tag
    obtain ⟨d',c',f',a',rfl,eqR⟩ := exactFields r fs valid target
    have eqQ : q = auxRaw dom cod fn arg := codeOfNode source
    have related : (row s.equivalentHeads (auxRaw dom cod fn arg) (auxRaw d' c' f' a')).1 = true := by
      rw [← eqQ,← eqR]
      simp only [edge,bits,Bool.and_eq_true] at edgeHeld
      exact edgeHeld.1.1.2
    rw [rowAuxPair] at related
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at related
    obtain ⟨⟨rfl,rfl⟩,row⟩ := related
    have atQ : admitted s ctx ty (auxRaw dom cod fn arg) = true := eqQ ▸ w.1
    have atR : admitted s ctx ty (auxRaw dom cod f' a') = true := eqR ▸ w.2
    have out := resultType s ctx ty dom cod fn arg atQ
    obtain rfl := out
    rw [admissionAux] at atQ atR
    simp only [Bool.and_eq_true] at atQ atR
    refine ⟨rfl,f',a',rfl,?_⟩
    rcases row with f | a
    · exact Or.inl ⟨moveChild s ctx (arrow dom cod) fn f' atQ.1.2 atR.1.2 f.1,f.2⟩
    · exact Or.inr ⟨a.1,moveChild s ctx dom arg a' atQ.2 atR.2 a.2⟩

#print axioms exact_LiteralTypedAuxExchangeCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxExchangeCasesProof
