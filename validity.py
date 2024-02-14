from z3 import * 
from FOL2tree import parse_text_FOL_to_tree
from Tree2SMT_LIB import fol_tree_to_smtlib, extract_variables

def check_fol_validity(premises, conclusion):
    # Initialize the solver
    solver = Solver()
    DicPredicates={}
    # Convert all premises to SMT-LIB and add to solver
    for premise in premises:
        #print(SetPredicates)
        variables=extract_variables(premise)
        premise_smtlib = fol_tree_to_smtlib(premise, variables,DicPredicates)
        #print(premise_smtlib)
        solver.add(parse_smt2_string(premise_smtlib))
    solver.push()
    # Parse the SMT-LIB string into a Z3 expression
    # Convert conclusion to SMT-LIB
    variables=extract_variables(conclusion)
    conclusion_smtlib = fol_tree_to_smtlib(conclusion,variables,DicPredicates)
    conclusionS = parse_smt2_string(conclusion_smtlib)
    negated_conclusion=Not(conclusionS[0])
    # Add the negation of the conclusion to the solver
    solver.add(negated_conclusion)

    # Check if the negated conclusion is unsatisfiable with the premises
    if solver.check() == unsat:
        return 'True'
    else:
        solver.pop()
        solver.add(conclusionS[0])
        if solver.check() == unsat:
            return 'False'
        else:
            return 'Unknown'
