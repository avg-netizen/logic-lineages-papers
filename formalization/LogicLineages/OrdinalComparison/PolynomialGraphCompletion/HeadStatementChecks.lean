module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.Targets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.WordSemanticProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadSourceProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadDerivedProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
public meta import LogicLineages.Audit

public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadStatementChecks

theorem call_compilation_correct : Targets.CallCompilationCorrect :=
  WordSemanticProof.callCompilationCorrect
theorem call_compilation_degree : Targets.CallCompilationDegree :=
  WordSemanticProof.callCompilationDegree
theorem polynomial_calls : Targets.PolynomialCalls := HeadSourceProof.polynomialCalls
theorem head_code_calibration : Targets.HeadCodeCalibration :=
  HeadProgramsProof.headCodeCalibration
theorem polynomial_head_coverage : Targets.PolynomialHeadCoverage :=
  HeadSourceProof.polynomialHeadCoverage
theorem head_graph_exact : Targets.HeadGraphExact := HeadSourceProof.headGraphExact
theorem head_graph_total_functional : Targets.HeadGraphTotalFunctional :=
  HeadDerivedProof.headGraphTotalFunctional head_graph_exact
theorem head_equation_exact : Targets.HeadEquationExact :=
  HeadDerivedProof.headEquationExact head_graph_exact
theorem finite_family_degree : Targets.FiniteFamilyDegree :=
  HeadDerivedProof.finiteFamilyDegree head_graph_exact
theorem head_programs : Targets.HeadPrograms := HeadProgramsProof.headPrograms

theorem full_polynomial_head_graphs : Targets.FullPolynomialHeadGraphs :=
  ⟨polynomial_head_coverage, head_graph_exact, head_graph_total_functional,
    head_equation_exact, finite_family_degree, head_programs⟩

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadStatementChecks
#audit_namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadStatementChecks
