import re
import nltk
from copy import deepcopy
import numpy as np
from nltk.tree import Tree
from itertools import product, combinations, permutations
from utils import *
import random
from z3 import *
from fuzzywuzzy import fuzz
from FOL2tree import parse_text_FOL_to_tree

def extract_variables(fol_str):
    variables = []
    for idx, char in enumerate(fol_str):
        if char in ['∀', '∃']:
            # Assumes the next character is the variable.
            # Make sure there are no spaces between quantifiers and variables.
            variables.append(fol_str[idx + 1])
    return variables
def CountArity(node):
    pivote=node
    #initially arity=1
    arity=1
    #if there is more than one term then terms has exactly 3 children (term , terms)
    #any times it happens, that means we have another term, we update pivote for the new terms (pivote[2]) 
    while(len(pivote)==3):
        arity+=1
        pivote=pivote[2]
    return arity

def formula(node,constants=None):
    if isinstance(node, str):  # Terminal node
        return node

    label = node.label()
    children = [formula(child) for child in node]

    if label == 'S':
        quant_part = children[0]
        body_part = children[1]
        # No need to close parenthesis here; it will be closed after the body part.
        return f'{quant_part} {body_part}'

    elif label == 'Q':
            # Extract quantifier and variable
            quant = children[0]
            var = children[1]
            # Start the quantifier string
            quant_str = f'({quant} (({var} Bool))'

            # Check if there's a nested 'Q' node
            if len(node) == 3:
                # Continue with the nested quantifiers without closing the current one
                nested_quant = formula(children[2])
                quant_str += f' {nested_quant}'
            else:
                # If there's no nested 'Q', we do not close the parenthesis here
                # It will be closed at the end of the assert statement
                quant_str += ' '

            return quant_str


    elif label == 'F':
        # Check for nested 'F' formulas and handle parentheses
        if len(children) == 3 and children[0] == '(' and children[2] == ')':
            # If the 'F' node is surrounded by parentheses, process the middle child.
            return formula(children[1])
        if children[0] == '¬':
            # If the 'F' starts with ¬, add Not and process.
            return formula(f'(not {formula(children[2])})')
        elif len(children) == 1:
            # Single child, could be a negation, an atomic formula, or a nested 'F'
            return formula(children[0])
        else:
            # Find 'OP' nodes and construct the binary operation, ignoring parentheses
            op_nodes = [child for child in node if isinstance(child, nltk.tree.Tree) and child.label() == 'OP']
            if op_nodes:
                # Assuming there's only one operator in the binary operation
                op_node = op_nodes[0]
                op_index = node.index(op_node)
                # Handle operands, skip the parentheses
                left = formula(node[op_index - 1])
                op = formula(op_node)  # Process the operator node
                right = formula(node[op_index + 1])
                return f'({op} {left} {right})'
            else:
                # Handle cases where 'F' is not a negation or binary operation
                return ' '.join([formula(child) for child in node if child not in ('(', ')')])

    elif label == 'OP':
        op_map = {'→': '=>', '∧': 'and', '∨': 'or', '↔': '=', '⊕': 'xor'}
        # Since OP will be a tree with a single string child, we get the operator from its first child
        smtlib_op = op_map.get(node[0], node[0])
        return smtlib_op

    elif label == 'QUANT':
        # Translate the quantifier to the SMT-LIB equivalent
        quantifier_map = {'∀': 'forall', '∃': 'exists'}
        smtlib_quant = quantifier_map.get(children[0], children[0])
        return smtlib_quant
    elif label == 'L':
        # Literal, could be a predicate or a negated predicate
        if children[0] == '¬':
            # Negated predicate, expects ['¬', 'PRED', '(', 'TERMS', ')']
            pred = children[1]
            terms = children[3]
            return f'(not ({pred} {terms}))'
        else:
            # Predicate, expects ['PRED', '(', 'TERMS', ')']
            pred = children[0]
            terms = children[2]
            return f'({pred} {terms})'

    elif label == 'PRED':
        # Predicate name, just return the name
        return children[0]

    elif label == 'TERMS':
        # Multiple terms, separated by commas
        # Remove commas and return space-separated terms
        terms = [child for child in children if child != ',']
        return ' '.join(terms)

    elif label == 'TERM':
        # A single term, could be a constant or a variable
        return children[0]

    elif label == 'CONST' or label == 'VAR':
        # Constant or variable, just return the name
        return children[0]

    # Add more cases as needed for other node types
    else:
        raise ValueError(f'Unknown node type: {label}')

def extract_predicates(premise, variables, DicPredicates):
    node = parse_text_FOL_to_tree(premise)
    constants = set([])
    def traverse(node):
        if isinstance(node, str):
            return

        label = node.label()
        children = [child for child in node]
        if label == 'CONST':
            if not (node[0] in variables):
                constants.add(node[0])
        if label == 'L':
            if len(node)==4:
                # Count arity based on the number of terms
                terms_node = children[2]  # This is the 'TERMS' node
                arity = CountArity(terms_node) #this function counts the arity
                # Extract predicate name
                pred_name = children[0][0]
                #leveinsteing distance to know if we have a new predicate
                new_word = replacement(pred_name, DicPredicates, arity)
                #if there is no changes it is because we have a predicate different from the ones in set
                if(new_word==pred_name):
                    # Add to predicates dictionary
                    DicPredicates[new_word] = arity
                #otherwise, pred_name is the same but with wrong written
                else:
                    children[0][0]=new_word
                

            elif len(node)==5:
                # Count arity based on the number of terms
                terms_node = children[3]  # This is the 'TERMS' node
                arity = CountArity(terms_node) #this function counts the arity
                pred_name = children[1][0]
                #leveinsteing distance to know if we have a new predicate
                new_word = replacement(pred_name, DicPredicates, arity)
                #if there is no changes it is because we have a predicate different from the ones in set
                if(new_word==pred_name):
                    # Add to predicates dictionary
                    DicPredicates[new_word] = arity
                #otherwise, pred_name is the same but with wrong written
                else:
                    children[1][0]=new_word

        for child in children:
            traverse(child)

    traverse(node)
    return [constants, node]

def generate_smtlib_declarations(predicates, constants):
    declarations = []
    for pred_name, arity in predicates.items():
        # Generate the type signature (Bool ...) based on arity
        type_signature = ' '.join(['Bool' for _ in range(arity)])
        declarations.append(f"(declare-fun {pred_name} ({type_signature}) Bool)")
    for c in constants:
        # Generate the type signature (Bool ...) based on arity
        type_signature = 'Bool'
        declarations.append(f"(declare-const {c} {type_signature} )")
    return '\n'.join(declarations)

#this function recives the premise we will convert into a tree
#variables to calculate the predicates of the premise
#we will transform the tree predicates according to the DicPredicates
#If a predicate in tree is 'similar' to someone from Dic we change for the one is in set
#Then we update the Dic with the new predicates
def fol_tree_to_smtlib(premise, variables, DicPredicates):
    # Now smtlib_str holds the entire SMT-LIB formula string
  constants, tree = extract_predicates(premise, variables, DicPredicates)
  predicates= DicPredicates 
  if len(tree)>1:
    quant_part = tree[0]
    body_part = tree[1]
    # This will hold the quantifier part of the SMT-LIB string
    quantifier_str = formula(quant_part)

    # This will hold the body part of the SMT-LIB string

    body_str = formula(body_part)

    # Now construct the final SMT-LIB string
    smtlib_str = f'(assert {quantifier_str} {body_str}'

        # Count the number of opened parentheses in the quantifier string to know how many to close
    num_open_parens = quantifier_str.count('(')
    num_close_parens = quantifier_str.count(')')
    difference = num_open_parens-num_close_parens
    # Close all parentheses at the end of the assert statement
    smtlib_str += ')' * (difference+1)
  else:
    body_part = tree[0]
    # This will hold the body part of the SMT-LIB string
    body_str = formula(body_part)
    smtlib_str = f'(assert {body_str})'
  
  declarations = generate_smtlib_declarations(predicates, constants)
  return declarations+'\n'+smtlib_str

# Function to create a mapping of words to predicates based on Levenshtein distance
#def replacement(predicate, Setpredicates):
#    replacement_dict = {}
#    s=len(predicate)
#    for pred in Setpredicates:
#        l=len(pred)
#        if ((l!=s) & (edit_dist(predicate, pred)<= 2)):
#            predicate = pred 
#            break
#    return predicate
def replacement(predicate, Dicpredicates,arity):
    for pred, n in Dicpredicates.items():
        partial_ratio = fuzz.partial_ratio(predicate, pred)
        if ((partial_ratio >= 85) & (n==arity)):
            predicate = pred
            break
    return predicate

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

def balance_parentheses(input_str):
    balanced = ""
    left_count = 0
    right_count = 0
    # count
    for char in input_str:
        if char == '(':
            left_count += 1
        elif char == ')':
            right_count += 1
        #if there are more right_count then we do not add the parenthesis, otherwise we add the char
        if left_count>=right_count:
            balanced+=char
    # At the end we check: if there are more left than right we add as many as needed
    difference=left_count-right_count 
    if difference>0:
        balanced+=')'*difference
    return balanced
