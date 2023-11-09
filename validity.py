from z3 import * 
from FOL2tree import parse_text_FOL_to_tree
from Tree2SMT-LIB import fol_tree_to_smtlib, extract_variables

def check_fol_validity(premises, conclusion):
    # Initialize the solver
    solver = Solver()

    # Convert all premises to SMT-LIB and add to solver
    for premise in premises:
        variables=extract_variables(premise)
        premise_tree = parse_text_FOL_to_tree(premise)
        premise_smtlib = fol_tree_to_smtlib(premise_tree, variables)
        #print(premise_smtlib)
        solver.add(parse_smt2_string(premise_smtlib))
      # Parse the SMT-LIB string into a Z3 expression
    # Convert conclusion to SMT-LIB
    conclusion_tree = parse_text_FOL_to_tree(conclusion)
    variables=extract_variables(conclusion)
    conclusion_smtlib = fol_tree_to_smtlib(conclusion_tree,variables)
    conclusionS = parse_smt2_string(conclusion_smtlib)
    #print(conclusionS)
    #print(solver)
    negated_conclusion=Not(conclusionS[0])
    # Add the negation of the conclusion to the solver
    solver.add(negated_conclusion)
    # Check if the negated conclusion is unsatisfiable with the premises
    if solver.check() == unsat:
        return 'True'
    elif solver.check() == sat:
        return 'False'
    else:
        return 'Unknown'
